open! Base

(* Execution device specific structure that decides the flattening/kernel allocation *)
module type ParallelizationStructure = sig
  type t
  type indexMode

  val default : t
  val tryToParallelize : t -> Nested.Expr.loopBlock -> (t * indexMode) option

  (* compares two parallelization structures and returns the 'better' one *)
  val compareStructures : indexMode list * indexMode list -> indexMode list
end

module ParallelizationStructureCUDA = struct
  type t =
    { availableThreads : int option
    ; availableBlocks : int option
    }
  [@@deriving sexp_of]

  (* outer loop shapes are appended to the start, cons *)
  (* (outer most loop is index 0, inner most - index n) *)
  type indexLoopNest = { indices : Nested.Expr.indexAlloc list } [@@deriving sexp_of]

  (* First number is the 'degree', number of dynamic shapes *)
  (* Second number is the 'constant' multiplier, comes from all the shapes that are constant *)
  (* The map part is the possible branches, like for Let and such *)
  type iterSpace = (int, int, Int.comparator_witness) Map.t

  let sexp_of_iterSpace iterSpace = Map.sexp_of_m__t (module Int) Int.sexp_of_t iterSpace

  (* Compute the 'polynomial degree' of an index space *)
  (* This is the index space of a single loop nest *)
  (* const is degree 0 *)
  (* x, y, z variables *)
  (* x = y = z is degree 1 *)
  (* product of n variables is degree n term *)
  (* result is a map of a degree and constant multiplier *)
  (* (loop 100) -> (0, 100) *)
  (* (loop 100 (loop x)) = (loop x (loop 100)) -> (1, 100) *)
  (* (loop y (loop 100 (loop x))) = (2, 100) *)
  let indexLoopNestPoly (a : indexLoopNest) : int * int =
    List.fold_right a.indices ~init:(0, 1) ~f:(fun idx (degree, mult) ->
      match idx with
      | Nested.Expr.Static i -> degree, mult * i
      | Nested.Expr.Dynamic _ -> degree + 1, mult)
  ;;

  let indexLoopNestListPoly (a : indexLoopNest list) : (int, int, _) Map.t =
    let polys = List.map ~f:indexLoopNestPoly a in
    let map =
      List.fold
        polys
        ~init:(Map.empty (module Int))
        ~f:(fun acc (degree, mult) ->
          Map.update acc degree ~f:(function
            | None -> mult
            | Some m2 -> m2 + mult))
    in
    map
  ;;

  (* Compare two lists that represent a polynomial and are sorted in decreasing order *)
  let rec comparePolyLists (a : (int * int) list) (b : (int * int) list) : int =
    match List.hd a, List.hd b with
    | Some (aDegree, aMult), Some (bDegree, bMult) ->
      if aDegree <> bDegree
      then aDegree - bDegree
      else if aMult <> bMult
      then aMult - bMult
      else comparePolyLists (List.tl_exn a) (List.tl_exn b)
    | None, Some _ -> -1
    | Some _, None -> 1
    | None, None -> 0
  ;;

  (* Compare two iteration spaces. *)
  (* Returns positive int if a is larger *)
  (* Returns negative int if b is larger *)
  (* Returns 0 if they are equal *)
  let compareIndexSpaceLists (a : indexLoopNest list) (b : indexLoopNest list) : int =
    let map_a = indexLoopNestListPoly a in
    let map_b = indexLoopNestListPoly b in
    let alist_a = Map.to_alist ?key_order:(Some `Decreasing) map_a in
    let alist_b = Map.to_alist ?key_order:(Some `Decreasing) map_b in
    comparePolyLists alist_a alist_b
  ;;

  type indexMode = Nested.Expr.indexMode [@@deriving sexp_of, equal, compare]

  type indexModeAlloc =
    { indexMode : indexMode
    ; loopBlockLabel : Identifier.t
    }
  [@@deriving sexp_of, equal, compare]

  type indexModeTree =
    (* list of allocations for each level of the tree.
       use max per level to calculate parallelism *)
    | FullPar of indexModeAlloc list list
    | Branches of indexModeTree list
  [@@deriving sexp_of, equal]

  (* TODO: those are some arbitrary numbers, we should derive them from device information *)

  let default = { availableThreads = Some 1024; availableBlocks = Some 65536 }

  (* Size of wapr, we don't want to allocate any extra beyond this *)
  let minimumThreads = 32

  (* Minimum number of threads we want to spawn to make this worthwhile *)
  let minimumTotalThreads = 1024 * 8

  (* TODO: some arbitrary maximum after which it's useless to try to load more work onto gpu *)
  let maximumTotalThreads = 1024 * 1024 * 8

  (* we don't want to do more iteration things than this because it might be better to run
     kernel multiple times at that point *)
  let maximumInnerSeqSpace = 10000

  (* TODO: why so low? *)
  let maxReduceThreads = 32
  let maxScanThreads = 256
  let maxScatterThreads = 256

  type shapeKnowledge =
    | Static of int
    | Dynamic of Nested.Index.shapeElement

  let intCeilDiv a b : int =
    let ceil = a / b in
    let remainder = Int.rem a b in
    if remainder = 0 then ceil else ceil + 1
  ;;

  let createStructure { availableThreads; availableBlocks } : t =
    match availableThreads, availableBlocks with
    | None, None -> { availableThreads; availableBlocks }
    | Some _, None ->
      raise (Unreachable.Error "Should not have threads without any blocks")
    | None, Some availableBlocks ->
      { availableThreads = None; availableBlocks = Some availableBlocks }
    | Some availableThreads, Some availableBlocks ->
      { availableThreads = Some availableThreads; availableBlocks = Some availableBlocks }
  ;;

  (* TODO: add some third option if we cannot allocate or sth *)
  let updateStructureWithIndexMode structure (index : indexMode) =
    let { availableThreads; availableBlocks } = structure in
    let Nested.Expr.{ allocatedThreads; allocatedBlocks } = index in
    let newAvailableThreads =
      match allocatedThreads with
      | None -> availableThreads
      | Some _ -> None
    in
    let newAvailableBlocks =
      match allocatedBlocks with
      | None -> availableBlocks
      | Some (Static allocatedBlocks) ->
        (match availableBlocks with
         | None -> None
         | Some availableBlocks -> Some (availableBlocks / allocatedBlocks))
      | Some (Dynamic allocatedBlocks) ->
        let mult =
          match allocatedBlocks with
          | Typed.Index.Add { const; refs } ->
            const + Map.fold refs ~init:0 ~f:(fun ~key:_ ~data acc -> acc + (data * 256))
          | Typed.Index.ShapeRef _ -> 256
        in
        (match availableBlocks with
         | None -> None
         | Some availableBlocks -> Some (availableBlocks / mult))
    in
    { availableThreads = newAvailableThreads; availableBlocks = newAvailableBlocks }
  ;;

  (* Tries to use the parallelization structure to try to parallelize the given loop block as much as possible
     For purely map loop blocks, it will parallelize with full respect to the resources, e.g. if no threads are
     available, it will not allocate any.
     For par consumer like reduce, it will need to allocate threads since it needs pretty specific memory locality.
     It is technically fine since consumer executes after the map body which would have used the threads and
     why we couldn't do the allocation in the first place.*)
  let tryToParallelize (structure : t) (lb : Nested.Expr.loopBlock) : indexMode option =
    let frameShape =
      match lb.frameShape with
      | Add { const; refs } ->
        if Map.is_empty refs then Static const else Dynamic (Add { const; refs })
      | ShapeRef ref -> Dynamic (ShapeRef ref)
    in
    let mapAlloc =
      let { availableThreads; availableBlocks } = structure in
      match availableThreads with
      | None ->
        (match availableBlocks with
         (* we ran out of parallelism*)
         | None -> None
         | Some availableBlocks ->
           (match frameShape with
            | Static size ->
              if size <= availableBlocks
              then
                Some
                  Nested.Expr.
                    { allocatedThreads = None
                    ; allocatedBlocks = Some (Static (Int.max 1 size))
                    }
              else None
            | Dynamic shapeElement ->
              Some
                Nested.Expr.
                  { allocatedThreads = None
                  ; allocatedBlocks = Some (Dynamic shapeElement)
                  }))
      | Some availableThreads ->
        (* we always use threads before blocks, so if we have threads we have blocks *)
        (match frameShape with
         | Static size ->
           if size < minimumThreads
           then None
           else if availableThreads < size
           then (
             (* TODO: check on the neededBlocks, because we might want to have
                fewer blocks that loop instead of having a lot of blocks *)
             (* TODO: do we ned ceil div here or normal works as well? *)
             let neededBlocks = intCeilDiv size availableThreads in
             let indexMode =
               Nested.Expr.
                 { allocatedThreads = Some (Nested.Expr.Static availableThreads)
                 ; allocatedBlocks = Some (Nested.Expr.Static neededBlocks)
                 }
             in
             Some indexMode)
           else
             (* TODO: we probably can not use up all threads occasionally, maybe that's good for something? *)
             Some { allocatedThreads = Some (Static size); allocatedBlocks = None }
         | Dynamic shapeElement ->
           Some { allocatedThreads = Some (Dynamic shapeElement); allocatedBlocks = None })
    in
    let consumerAlloc =
      let { availableThreads; availableBlocks } = structure in
      match lb.consumer with
      | None -> None
      (* cannot really parallelize fold *)
      | Some (Fold _) -> None
      | Some (Reduce _ as consumer) | Some (Scatter _ as consumer) ->
        let maxThreadsConsumer =
          match consumer with
          | Reduce { arg = _; zero = _; body = _; d = _; character; type' = _ } ->
            (match character with
             | Reduce -> maxReduceThreads
             | Scan -> maxScanThreads)
          | Scatter _ -> maxScatterThreads
          | Fold _ -> raise Unreachable.default
        in
        let maxThreads =
          match availableThreads with
          | None -> maxThreadsConsumer
          | Some availableThreads -> Int.min availableThreads maxThreadsConsumer
        in
        (match availableBlocks with
         (* We ran out of parallelism *)
         | None -> None
         | Some availableBlocks ->
           (match frameShape with
            | Static size ->
              if size >= maxThreads * availableBlocks
                 (* we don't have enough parallelism to allocate at all *)
              then None
              else (
                (* We have to have blocks if we have threads *)
                let usedThreads = Int.max 1 (Int.min size maxThreads) in
                let neededBlocks = intCeilDiv (Int.max 1 size) usedThreads in
                Some
                  Nested.Expr.
                    { allocatedThreads = Some (Static usedThreads)
                    ; allocatedBlocks = Some (Static neededBlocks)
                    })
            | Dynamic shapeElement ->
              Some
                Nested.Expr.
                  { allocatedThreads = Some (Static maxThreads)
                  ; allocatedBlocks = Some (Dynamic shapeElement)
                  }))
    in
    let index =
      match mapAlloc, consumerAlloc with
      | None, None -> None
      | Some i, None ->
        (match lb.consumer with
         | None -> Some i
         | Some _ ->
           (* we could not parallelize consumer so we cannot do any parallel things here *)
           None)
      | None, Some i ->
        (match frameShape with
         | Dynamic _ -> raise Unimplemented.default
         | Static size -> if size < minimumThreads then None else Some i)
      | ( Some { allocatedThreads = _; allocatedBlocks = _ }
        , Some { allocatedThreads; allocatedBlocks } ) ->
        (* I think this is a good enough approximation that will work for now, *)
        (* as consumer is more more 'finicky' thing here.  *)
        Some { allocatedThreads; allocatedBlocks }
    in
    index
  ;;

  let updateStructureWithIndexModeList (structure : t) (indexModeTree : indexMode list) =
    List.fold indexModeTree ~init:structure ~f:updateStructureWithIndexMode
  ;;

  let rec hasBeenParallelized (i : indexModeTree) : bool =
    match i with
    | FullPar tree -> not (List.is_empty tree)
    | Branches branches -> List.exists branches ~f:(fun b -> hasBeenParallelized b)
  ;;

  let compareIndexAlloc (a : indexModeAlloc) (b : indexModeAlloc) =
    let a = a.indexMode in
    let b = b.indexMode in
    (* For now we'll assume that any dynamic shape is larger than any static one *)
    (* But we should be able to collect a better approximation for this by analyzing the program *)
    match a, b with
    | ( { allocatedThreads = at; allocatedBlocks = ab }
      , { allocatedThreads = bt; allocatedBlocks = bb } ) ->
      let a = List.filter_map ~f:(fun x -> x) [ at; ab ] in
      let b = List.filter_map ~f:(fun x -> x) [ bt; bb ] in
      compareIndexSpaceLists [ { indices = a } ] [ { indices = b } ]
  ;;

  let updateStructureWithIndexModeTree (structure : t) (indexModeTree : indexModeTree) =
    match indexModeTree with
    | FullPar tree ->
      let maxAllocPerLevel =
        List.filter_map tree ~f:(fun levelIndices ->
          List.max_elt levelIndices ~compare:compareIndexAlloc)
      in
      let maxAllocPerLevelIndexModes =
        List.map maxAllocPerLevel ~f:(fun a -> a.indexMode)
      in
      updateStructureWithIndexModeList structure maxAllocPerLevelIndexModes
    | Branches branches ->
      let canExtend = not (hasBeenParallelized (Branches branches)) in
      if canExtend
      then (* we haven't parallelized yet so we haven't used any resources *)
        structure
      else { availableBlocks = None; availableThreads = None }
  ;;

  let rec indexModeTreeToIndexLoopNests (i : indexModeTree) : indexLoopNest list =
    match i with
    | FullPar tree ->
      let maxAllocPerLevel =
        List.filter_map tree ~f:(fun levelIndices ->
          List.max_elt levelIndices ~compare:compareIndexAlloc)
      in
      let maxAllocPerLevelIndexAllocs =
        List.filter_map
          maxAllocPerLevel
          ~f:
            (fun
              { indexMode = { allocatedThreads; allocatedBlocks }; loopBlockLabel = _ } ->
            match allocatedThreads, allocatedBlocks with
            | None, None -> None
            | Some a, None | None, Some a -> Some a
            | Some (Static t), Some (Static b) -> Some (Static (t * b))
            | _ -> raise Unimplemented.default)
      in
      [ { indices = maxAllocPerLevelIndexAllocs } ]
    | Branches branches -> List.concat_map ~f:indexModeTreeToIndexLoopNests branches
  ;;

  let compareIndexTreesIterationSpace (a : indexModeTree) (b : indexModeTree) : int =
    compareIndexSpaceLists
      (indexModeTreeToIndexLoopNests a)
      (indexModeTreeToIndexLoopNests b)
  ;;

  (* a and b are index mode trees that dictate how the loopblocks are to be parallelized.
     a_inner and b_inner are.
     Assuming that the trees are 'complete', that is no more parallelization is going to be added on top.
     Assuming that the 2 trees have been constructed over the same AST/iteration space.
     The heuristic's rough cost model is: the better tree is one that leaves less inner seq nodes
     and parallelizes more (both of them are techically the same because of the assumption) *)
  let compareStructures
    (a : indexModeTree)
    (b : indexModeTree)
    (a_inner : iterSpace)
    (b_inner : iterSpace)
    : indexModeTree option
    =
    let comparison = compareIndexTreesIterationSpace a b in
    let a_inner_list = Map.to_alist ?key_order:(Some `Increasing) a_inner in
    let b_inner_list = Map.to_alist ?key_order:(Some `Increasing) b_inner in
    let a_inner_larger = comparePolyLists a_inner_list b_inner_list in
    let a_inner_const = List.fold a_inner_list ~init:0 ~f:(fun acc (_, v) -> acc + v) in
    let a_inner_under_bound = a_inner_const <= maximumInnerSeqSpace in
    let b_inner_const = List.fold b_inner_list ~init:0 ~f:(fun acc (_, v) -> acc + v) in
    let b_inner_under_bound = b_inner_const <= maximumInnerSeqSpace in
    let a_strictly_better = comparison > 0 && a_inner_under_bound in
    let b_strictly_better = comparison < 0 && b_inner_under_bound in
    (* TODO: don't check total iter space, instead look at maximum depth of all subtrees and go from there *)
    if a_strictly_better
    then Some a (* a has more parallelism and is below limit so it's better *)
    else if b_strictly_better
    then Some b
    else if a_inner_under_bound && a_inner_larger > 0
    then Some a (* a has more inner instructions and below the limit so it's better *)
    else if a_inner_under_bound && a_inner_larger < 0
    then Some b (* b has more inner instructions and below the limit so it's better *)
    else if a_inner_larger = 0
    then Some a (* a and b are basically the same so we just return one of them*)
    else if a_inner_under_bound
    then Some a (* a has smaller inner space but it fits so it's better *)
    else if b_inner_under_bound
    then Some b (* same as above but for b *)
    else if a_inner_larger < 0
    then Some a (* too many in both, so we choose the smaller one *)
    else Some b
  ;;

  let appendIndexToTree index indexModeTree =
    match indexModeTree with
    | FullPar tree -> Some (FullPar (index :: tree))
    | Branches branches ->
      let canExtend = not (hasBeenParallelized (Branches branches)) in
      if canExtend then Some (FullPar [ index ]) else None
  ;;

  let emptyIndexTree = FullPar []

  type viabilityResult =
    | Done
    | Working of int

  let isViableKernel (i : indexModeTree) : bool =
    (* a viable kernel is one that either has at least minimumIterationSpace of iterations *)
    (* or at least one dynamic shape (will be decided at compile time) *)
    let rec isViableHelper (i : indexModeTree) : viabilityResult =
      match i with
      | FullPar tree ->
        List.fold tree ~init:(Working 0) ~f:(fun acc branch ->
          match acc with
          | Done -> Done
          | Working n ->
            let maxBranch = List.max_elt branch ~compare:compareIndexAlloc in
            (match maxBranch with
             | None -> acc
             | Some
                 { indexMode = { allocatedThreads; allocatedBlocks }; loopBlockLabel = _ }
               ->
               let alloc =
                 List.filter_map ~f:(fun x -> x) [ allocatedThreads; allocatedBlocks ]
               in
               let res =
                 List.fold alloc ~init:(Working 0) ~f:(fun acc a ->
                   match acc with
                   | Done -> Done
                   | Working n ->
                     (match a with
                      | Static n2 -> Working (Int.max n n2)
                      | Dynamic _ -> Done))
               in
               (match res with
                | Done -> Done
                | Working nb ->
                  if n * nb >= minimumTotalThreads then Done else Working (n * nb))))
      | Branches b ->
        let foo = List.map b ~f:isViableHelper in
        if List.exists foo ~f:(function
             | Done -> true
             | _ -> false)
        then Done
        else
          Working
            (List.fold foo ~init:0 ~f:(fun acc a ->
               match a with
               | Working n -> n + acc
               | Done -> acc))
    in
    let res = isViableHelper i in
    match res with
    | Done -> true
    | Working n -> n >= minimumTotalThreads
  ;;

  (* Parallelism bracket for MapKernel - find the closest number that's smaller than *)
  (* the total parallelism of a kernel, and use the RHS tuple to allocate (blocks, threads) *)
  let parallelismBracketsForMapKernel : (int, int * int, _) Map.t =
    let maxThreads = 1024 in
    Map.of_alist_exn
      (module Int)
      [ 8192, (8192 / maxThreads, maxThreads)
      ; 16384, (16384 / maxThreads, maxThreads)
      ; 65536, (65536 / maxThreads, maxThreads)
      ; 262144, (262144 / maxThreads, maxThreads)
      ; 1048576, (1048576 / maxThreads, maxThreads)
      ; 8388608, (8388608 / maxThreads, maxThreads)
      ]
  ;;

  (* Parallelism bracket for LoopKernel - find the closest number that's smaller than *)
  (* the total parallelism of a kernel, and use the RHS tuple to allocate (blocks, threads) *)
  let parallelismBracketsForLoopKernel (consumer : Nested.Expr.consumerOp)
    : (int, int * int, _) Map.t
    =
    let maxThreads =
      match consumer with
      | Nested.Expr.Reduce r ->
        (match r.character with
         | Reduce -> maxReduceThreads
         | Scan -> maxScanThreads)
      | Nested.Expr.Fold _ -> 0
      | Nested.Expr.Scatter _ -> maxScatterThreads
    in
    Map.of_alist_exn
      (module Int)
      [ 8192, (8192 / maxThreads, maxThreads)
      ; 16384, (16384 / maxThreads, maxThreads)
      ; 65536, (65536 / maxThreads, maxThreads)
      ; 262144, (262144 / maxThreads, maxThreads)
      ; 1048576, (1048576 / maxThreads, maxThreads)
      ; 8388608, (8388608 / maxThreads, maxThreads)
      ]
  ;;

  let constantPoly : iterSpace = Map.singleton (module Int) 0 1
  let zeroPoly : iterSpace = Map.singleton (module Int) 0 0

  let polyMultDim (poly : iterSpace) (dim : Nested.Index.shapeElement) : iterSpace =
    match dim with
    | Typed.Index.Add { const; refs } ->
      if Map.is_empty refs
      then Map.map poly ~f:(fun v -> v * const)
      else (
        let totalUnknown =
          Map.fold refs ~init:0 ~f:(fun ~key:_ ~data acc -> acc + data)
        in
        poly
        |> Map.map ~f:(fun v -> v * const * totalUnknown)
        |> Map.map_keys_exn (module Int) ~f:(fun k -> k + 1))
    | Typed.Index.ShapeRef _ -> Map.map_keys_exn (module Int) poly ~f:(fun k -> k + 1)
  ;;

  let combinePolys (a : iterSpace) (b : iterSpace) : iterSpace =
    Map.merge_skewed a b ~combine:(fun ~key:_ v1 v2 -> v1 + v2)
  ;;

  (* Computers the iteration space of a given expression. *)
  let rec exprToPoly (expr : Nested.t) : iterSpace =
    match expr with
    | Ref _ -> constantPoly
    | Frame _ -> constantPoly
    | BoxValue { box; type' = _ } -> exprToPoly box
    | IndexLet { indexArgs = _; body; type' = _ } -> exprToPoly body
    | ReifyIndex _ -> constantPoly
    | ShapeProd _ -> constantPoly
    | Let { args; body; type' = _ } ->
      let args = List.map args ~f:(fun a -> a.value) in
      exprListToPoly (body :: args)
    | LoopBlock
        { label = _
        ; frameShape
        ; mapArgs = _
        ; mapIotas = _
        ; mapBody
        ; mapBodyMatcher = _
        ; mapResults = _
        ; consumer
        ; type' = _
        } ->
      let mapBodyPoly = exprToPoly mapBody in
      let mapBodyPoly = polyMultDim mapBodyPoly frameShape in
      (match consumer with
       | Some consumer ->
         let bodyPoly, zeroPoly = consumerToPoly consumer in
         let bodyPoly = polyMultDim bodyPoly frameShape in
         List.fold
           [ bodyPoly; zeroPoly; mapBodyPoly ]
           ~init:(Map.empty (module Int))
           ~f:(fun a b -> Map.merge_skewed a b ~combine:(fun ~key:_ v1 v2 -> v1 + v2))
       | None -> mapBodyPoly)
    | Box { indices = _; body; bodyType = _; type' = _ } -> exprToPoly body
    | Literal _ -> constantPoly
    | Values { elements; type' = _ } -> exprListToPoly elements
    | ScalarPrimitive { op = _; args; type' = _ } -> exprListToPoly args
    | TupleDeref { index = _; tuple; type' = _ } -> exprToPoly tuple
    | ContiguousSubArray
        { arrayArg; indexArg; originalShape = _; resultShape = _; type' = _ } ->
      exprListToPoly [ arrayArg; indexArg ]
    | Append { args; type' = _ } -> exprListToPoly args
    | Zip { zipArg; nestCount = _; type' = _ } -> exprToPoly zipArg
    | Unzip { unzipArg; type' = _ } -> exprToPoly unzipArg

  (* Left iterSpace is the body, Right iterSpace is the zero *)
  and consumerToPoly (consumer : Nested.Expr.consumerOp) : iterSpace * iterSpace =
    match consumer with
    | Nested.Expr.Reduce { arg = _; zero; body; d = _; character = _; type' = _ } ->
      exprToPoly body, exprToPoly zero
    | Nested.Expr.Fold
        { zeroArg; arrayArgs = _; body; reverse = _; d = _; character = _; type' = _ } ->
      exprToPoly body, exprToPoly zeroArg.zeroValue
    | Nested.Expr.Scatter _ -> constantPoly, constantPoly

  and exprListToPoly (elements : Nested.t list) : iterSpace =
    elements
    |> List.map ~f:exprToPoly
    |> List.fold ~init:(Map.empty (module Int)) ~f:combinePolys
  ;;
end

type cuda_t = ParallelizationStructureCUDA.t [@@deriving sexp_of]

type index_cuda_t = ParallelizationStructureCUDA.indexMode
[@@deriving sexp_of, equal, compare]

type index_cuda_alloc_t = ParallelizationStructureCUDA.indexModeAlloc
[@@deriving sexp_of, equal, compare]

type index_tree_cuda_t = ParallelizationStructureCUDA.indexModeTree
[@@deriving sexp_of, equal]

type iterSpace = ParallelizationStructureCUDA.iterSpace [@@deriving sexp_of]

let tryToParallelizeCUDA = ParallelizationStructureCUDA.tryToParallelize
let defaultCUDA = ParallelizationStructureCUDA.default

let parallelismBracketsForMapKernel =
  ParallelizationStructureCUDA.parallelismBracketsForMapKernel
;;

let parallelismBracketsForLoopKernel =
  ParallelizationStructureCUDA.parallelismBracketsForLoopKernel
;;

let updateStructureWithIndexModeTree =
  ParallelizationStructureCUDA.updateStructureWithIndexModeTree
;;

let createIndexModeAlloc ~label ~indexMode : ParallelizationStructureCUDA.indexModeAlloc =
  ParallelizationStructureCUDA.{ loopBlockLabel = label; indexMode }
;;

let compareStructures = ParallelizationStructureCUDA.compareStructures
let appendIndexToTree = ParallelizationStructureCUDA.appendIndexToTree
let emptyIndexTree = ParallelizationStructureCUDA.emptyIndexTree
let hasBeenParallelized = ParallelizationStructureCUDA.hasBeenParallelized
let branches branchList = ParallelizationStructureCUDA.Branches branchList
let isViableKernel tree = ParallelizationStructureCUDA.isViableKernel tree
let exprIterSpace = ParallelizationStructureCUDA.exprToPoly
let consumerIterSpace = ParallelizationStructureCUDA.consumerToPoly
let constantIterSpace = ParallelizationStructureCUDA.constantPoly
let zeroIterSpace = ParallelizationStructureCUDA.zeroPoly

let addIterSpaces (a : iterSpace) (b : iterSpace) =
  ParallelizationStructureCUDA.combinePolys a b
;;

let iterSpaceMultDim (a : iterSpace) (d : Nested.Index.shapeElement) =
  ParallelizationStructureCUDA.polyMultDim a d
;;

let minimumViableKernelParallelism = ParallelizationStructureCUDA.minimumTotalThreads
