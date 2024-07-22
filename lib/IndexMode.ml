open! Base

(* Execution device specific structure that decides the flattening/kernel allocation *)
module type ParallelizationStructure = sig
  type t
  type indexMode

  val default : t

  (* TODO: what happens if we cannot nest on current level *)
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
  let minimumTotalThreads = 1024

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

  let mergeIndexModes (a : indexMode) (b : indexMode) =
    let mergeAllocatedThreads =
      match a.allocatedThreads, b.allocatedThreads with
      | None, None -> None
      | Some num, None | None, Some num -> Some num
      | Some a, Some b -> Some (Int.max a b)
    in
    let mergeAllocatedBlocks =
      match a.allocatedBlocks, b.allocatedBlocks with
      | None, None -> None
      | Some num, None | None, Some num -> Some num
      | Some a, Some b -> Some (Int.max a b)
    in
    Nested.Expr.
      { allocatedThreads = mergeAllocatedThreads; allocatedBlocks = mergeAllocatedBlocks }
  ;;

  (* TODO: add some third option if we cannot allocate or sth *)
  let updateStructureWithIndexMode structure (index : indexMode) =
    let open Nested.Expr in
    let { availableThreads; availableBlocks } = structure in
    let { allocatedThreads; allocatedBlocks } = index in
    let newAvailableThreads =
      match allocatedThreads with
      | None -> availableThreads
      | Some _ -> None
    in
    let newAvailableBlocks =
      match allocatedBlocks with
      | None -> availableBlocks
      | Some allocatedBlocks ->
        (match availableBlocks with
         | None -> None
         | Some availableBlocks -> Some (availableBlocks / allocatedBlocks))
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
                    { allocatedThreads = None; allocatedBlocks = Some (Int.max 1 size) }
              else None
            | Dynamic _ -> None))
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
                 { allocatedThreads = Some availableThreads
                 ; allocatedBlocks = Some neededBlocks
                 }
             in
             Some indexMode)
           else
             (* TODO: we probably can not use up all threads occasionally, maybe that's good for something? *)
             Some { allocatedThreads = Some size; allocatedBlocks = None }
         | Dynamic _ -> None)
    in
    let consumerAlloc =
      let { availableThreads; availableBlocks } = structure in
      match lb.consumer with
      | None -> None
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
                    { allocatedThreads = Some usedThreads
                    ; allocatedBlocks = Some neededBlocks
                    })
            | Dynamic _ -> None))
      (* cannot really parallelize fold *)
      | Some (Fold _) -> None
    in
    let index =
      match mapAlloc, consumerAlloc with
      | None, None -> None
      | Some i, None ->
        (match lb.consumer with
         | None ->
           Some i
           (* we could not parallelize consumer so we cannot do any parallel things here *)
         | Some _ -> None)
      | None, Some i ->
        (match frameShape with
         | Dynamic _ -> raise Unimplemented.default
         | Static size -> if size < minimumThreads then None else Some i)
      | ( Some
            { allocatedThreads = allocatedThreadsMap
            ; allocatedBlocks = allocatedBlocksMap
            }
        , Some
            { allocatedThreads = allocatedThreadsConsumer
            ; allocatedBlocks = allocatedBlocksConsumer
            } ) ->
        (* minimize the threads and maximize the blocks? *)
        let allocatedThreads =
          match allocatedThreadsMap, allocatedThreadsConsumer with
          | None, None | Some _, None | None, Some _ -> None
          | Some t1, Some t2 -> Some (min t1 t2)
        in
        let allocatedBlocks =
          match allocatedBlocksMap, allocatedBlocksConsumer with
          | None, None | Some _, None | None, Some _ -> None
          | Some t1, Some t2 -> Some (max t1 t2)
        in
        Some { allocatedThreads; allocatedBlocks }
    in
    index
  ;;

  (* List has recent-most or 'upper level' allocation first, so
     last is the most nested/oldest. *)
  let mergeIndexModeTrees (a : indexMode list) (b : indexMode list) =
    let rec mergeIndexModeTreesAcc
      (a : indexMode list)
      (b : indexMode list)
      (acc : indexMode list)
      =
      match a, b with
      | [], [] -> acc
      | hd :: tl, [] | [], hd :: tl -> mergeIndexModeTreesAcc tl [] (hd :: acc)
      | hd_a :: tl_a, hd_b :: tl_b ->
        mergeIndexModeTreesAcc tl_a tl_b (mergeIndexModes hd_a hd_b :: acc)
    in
    mergeIndexModeTreesAcc a b []
  ;;

  let mergeIndexModeAllocTrees
    (a : indexModeAlloc list list)
    (b : indexModeAlloc list list)
    =
    let rec mergeIndexModeTreesAcc
      (a : indexModeAlloc list list)
      (b : indexModeAlloc list list)
      (acc : indexModeAlloc list list)
      =
      match a, b with
      | [], [] -> acc
      | hd :: tl, [] | [], hd :: tl -> mergeIndexModeTreesAcc tl [] (hd :: acc)
      | hd_a :: tl_a, hd_b :: tl_b ->
        mergeIndexModeTreesAcc tl_a tl_b (List.append hd_a hd_b :: acc)
    in
    mergeIndexModeTreesAcc a b []
  ;;

  let updateStructureWithIndexModeTree (structure : t) (indexModeTree : indexMode list) =
    List.fold indexModeTree ~init:structure ~f:updateStructureWithIndexMode
  ;;

  let calcIterationSpaceIndexList (i : indexMode list) : int =
    let threads =
      List.fold i ~init:0 ~f:(fun acc { allocatedThreads; allocatedBlocks = _ } ->
        match allocatedThreads with
        | None -> acc
        | Some i -> i + acc)
    in
    let blocks =
      List.fold i ~init:1 ~f:(fun acc { allocatedThreads = _; allocatedBlocks } ->
        match allocatedBlocks with
        | None -> acc
        | Some i -> i * acc)
    in
    threads * blocks
  ;;

  let rec hasBeenParallelized (i : indexModeTree) : bool =
    match i with
    | FullPar tree -> not (List.is_empty tree)
    | Branches branches -> List.exists branches ~f:(fun b -> hasBeenParallelized b)
  ;;

  let updateStructureWithIndexModeTree (structure : t) (indexModeTree : indexModeTree) =
    match indexModeTree with
    | FullPar tree ->
      updateStructureWithIndexModeTree
        structure
        (List.filter_map tree ~f:(function
          | [] -> None
          | hd :: tl ->
            Some
              (List.fold tl ~init:hd.indexMode ~f:(fun acc i ->
                 if calcIterationSpaceIndexList [ acc ]
                    >= calcIterationSpaceIndexList [ i.indexMode ]
                 then acc
                 else i.indexMode))))
    | Branches branches ->
      let canExtend = not (hasBeenParallelized (Branches branches)) in
      if canExtend
      then (* we haven't parallelized yet so we haven't used any resources *)
        structure
      else { availableBlocks = None; availableThreads = None }
  ;;

  let rec calcIterationSpace (i : indexModeTree) : int =
    match i with
    | FullPar tree ->
      calcIterationSpaceIndexList
        (List.filter_map tree ~f:(function
          | [] -> None
          | hd :: tl ->
            Some
              (List.fold tl ~init:hd.indexMode ~f:(fun acc i ->
                 if calcIterationSpaceIndexList [ acc ]
                    >= calcIterationSpaceIndexList [ i.indexMode ]
                 then acc
                 else i.indexMode))))
    | Branches branches ->
      List.fold branches ~init:0 ~f:(fun acc b -> acc + calcIterationSpace b)
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
    (a_inner : int)
    (b_inner : int)
    : indexModeTree option
    =
    let a_iteration_total = calcIterationSpace a in
    let b_iteration_total = calcIterationSpace b in
    let a_strictly_better =
      a_iteration_total > b_iteration_total
      (* && a_iteration_total <= maximumTotalThreads *)
      && a_inner <= maximumInnerSeqSpace
    in
    let b_strictly_better =
      b_iteration_total > a_iteration_total
      (* && b_iteration_total <= maximumTotalThreads *)
      && b_inner <= maximumInnerSeqSpace
    in
    (* TODO: don't check total iter space, instead look at maximum depth of all subtrees and go from there *)
    if a_strictly_better
    then Some a (* a has more parallelism and is below limit so it's better *)
    else if b_strictly_better
    then Some b
    else if a_inner < maximumInnerSeqSpace && a_inner > b_inner
    then Some a (* a has more inner instructions and below the limit so it's better *)
    else if b_inner < maximumInnerSeqSpace && b_inner > a_inner
    then Some b (* b has more inner instructions and below the limit so it's better *)
    else if a_inner = b_inner
    then Some a (* a and b are basically the same so we just return one of them*)
    else if a_inner < maximumInnerSeqSpace
    then Some a (* a has smaller inner space but it fits so it's better *)
    else if b_inner < maximumInnerSeqSpace
    then Some b (* same as above but for b *)
    else if a_inner < b_inner
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
end

type cuda_t = ParallelizationStructureCUDA.t [@@deriving sexp_of]

type index_cuda_t = ParallelizationStructureCUDA.indexMode
[@@deriving sexp_of, equal, compare]

type index_cuda_alloc_t = ParallelizationStructureCUDA.indexModeAlloc
[@@deriving sexp_of, equal, compare]

type index_tree_cuda_t = ParallelizationStructureCUDA.indexModeTree
[@@deriving sexp_of, equal]

let tryToParallelizeCUDA = ParallelizationStructureCUDA.tryToParallelize
let defaultCUDA = ParallelizationStructureCUDA.default
let mergeIndexModes = ParallelizationStructureCUDA.mergeIndexModes

let updateStructureWithIndexMode =
  ParallelizationStructureCUDA.updateStructureWithIndexMode
;;

let updateStructureWithIndexModeTree =
  ParallelizationStructureCUDA.updateStructureWithIndexModeTree
;;

let createIndexModeAlloc ~label ~indexMode : ParallelizationStructureCUDA.indexModeAlloc =
  ParallelizationStructureCUDA.{ loopBlockLabel = label; indexMode }
;;

let mergeIndexModeTrees = ParallelizationStructureCUDA.mergeIndexModeTrees
let mergeIndexModeAllocTrees = ParallelizationStructureCUDA.mergeIndexModeAllocTrees
let compareStructures = ParallelizationStructureCUDA.compareStructures
let appendIndexToTree = ParallelizationStructureCUDA.appendIndexToTree
let emptyIndexTree = ParallelizationStructureCUDA.emptyIndexTree
let hasBeenParallelized = ParallelizationStructureCUDA.hasBeenParallelized
let branches branchList = ParallelizationStructureCUDA.Branches branchList
