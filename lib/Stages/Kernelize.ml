open! Base
module Index = Corn.Index
module Type = Corn.Type

type host = Corn.Expr.host [@@deriving sexp_of]
type device = Corn.Expr.device [@@deriving sexp_of]

module ParallelismShape = struct
  (** Describes the shape of parallelism in an expression. *)
  type t =
    | Known of int
    | ParallelAcrossDim of
        { dim : Index.shapeElement
        ; rest : t
        ; parallelismFloor : int
        }
    | MaxParallelism of
        { maxAcross : t list
        ; parallelismFloor : int
        }
  [@@deriving sexp_of]

  let parallelismFloor = function
    | Known n -> n
    | ParallelAcrossDim p -> p.parallelismFloor
    | MaxParallelism p -> p.parallelismFloor
  ;;

  let known = function
    | Known n -> Some n
    | ParallelAcrossDim _ -> None
    | MaxParallelism _ -> None
  ;;

  let nestParallelism (shapeElement : Index.shapeElement) restParallelism =
    match shapeElement, known restParallelism with
    | Add { const; refs }, Some rest when Map.is_empty refs -> Known (const * rest)
    | _ ->
      let minParallelismOfTopDim =
        match shapeElement with
        | Add { const; refs = _ } -> const
        | ShapeRef _ -> 0
      in
      ParallelAcrossDim
        { dim = shapeElement
        ; rest = restParallelism
        ; parallelismFloor = minParallelismOfTopDim * parallelismFloor restParallelism
        }
  ;;

  let singleDimensionParallelism shapeElement = nestParallelism shapeElement (Known 1)
  let empty = Known 1

  let max pars =
    let rec flatten l =
      List.bind l ~f:(function
        | MaxParallelism p -> flatten p.maxAcross
        | p -> [ p ])
    in
    let pars = flatten pars in
    let maxKnown =
      pars |> List.map ~f:known |> List.filter_opt |> List.max_elt ~compare:Int.compare
    in
    let pars =
      match maxKnown with
      | Some maxKnown ->
        Known maxKnown
        :: List.filter_map pars ~f:(function
          | Known _ -> None
          | p -> Some p)
      | None -> pars
    in
    match flatten pars with
    | [] -> Known 0
    | [ par ] -> par
    | maxAcrossHead :: maxAcrossRest ->
      let parallelismFloor =
        maxAcrossHead :: maxAcrossRest
        |> NeList.map ~f:parallelismFloor
        |> NeList.max_elt ~compare:Int.compare
      in
      let maxAcross = maxAcrossHead :: maxAcrossRest in
      MaxParallelism { maxAcross; parallelismFloor }
  ;;

  let rec toCorn : t -> Corn.Expr.parallelism = function
    | Known n -> KnownParallelism n
    | ParallelAcrossDim p -> Parallelism { shape = p.dim; rest = toCorn p.rest }
    | MaxParallelism p -> MaxParallelism (List.map p.maxAcross ~f:toCorn)
  ;;
end

(** For a Nested expression, the best host and device Corn expressions
    that it can be compiled into. *)
type compilationOptions =
  { hostExpr : host Corn.Expr.t
  ; deviceExpr : device Corn.Expr.t
  ; hostParShape : ParallelismShape.t
      (** The expression if it were to be the body of a map kernel,
          enabling flattening *)
  ; flattenedMapBody : Corn.Expr.mapBody
  ; flattenedMapBodyParShape : ParallelismShape.t
  }
[@@deriving sexp_of]

let compilationOptions ~hostExpr ~deviceExpr ~hostParShape =
  { hostExpr
  ; deviceExpr
  ; hostParShape
  ; flattenedMapBody = MapBodyExpr deviceExpr
  ; flattenedMapBodyParShape = Known 1
  }
;;

let hostExpr { hostExpr; _ } = hostExpr
let deviceExpr { deviceExpr; _ } = deviceExpr
let hostParShape { hostParShape; _ } = hostParShape

module ParallelismWorthwhileness = struct
  type t =
    | NotWorthwhile of { bound : int option }
    | Worthwhile of { bound : int option }
    | Saturating
  [@@deriving sexp_of]

  let saturatationCutoff device = DeviceInfo.maxThreads device

  let worthwhileParallelismCutoff (_ : DeviceInfo.t) =
    (* Arbitrary heuristic I came up with with no testing.
       A good heuristic should factor in both host and device info. *)
    128
  ;;

  let get deviceInfo p =
    if ParallelismShape.parallelismFloor p >= saturatationCutoff deviceInfo
    then Saturating
    else if ParallelismShape.parallelismFloor p >= worthwhileParallelismCutoff deviceInfo
    then Worthwhile { bound = ParallelismShape.known p }
    else NotWorthwhile { bound = ParallelismShape.known p }
  ;;
end

let rec getIterationSpace (expr : Nested.t) : int =
  match expr with
  | Literal _ -> 1
  | ScalarPrimitive _ -> 1
  | Ref _ -> 1
  | Frame { elements; dimension = _; type' = _ } -> getIterationSpaceList elements
  | BoxValue bv -> getIterationSpace bv.box
  | IndexLet { indexArgs; body; type' = _ } ->
    let tArgs =
      List.map
        ~f:(fun { indexValue; indexBinding = _; sort = _ } ->
          match indexValue with
          | Runtime t -> t
          | FromBox { box; i = _ } -> box)
        indexArgs
    in
    getIterationSpaceList (body :: tArgs)
  | ReifyIndex _ -> 1
  | ShapeProd _ -> 1
  | Let { args; body; type' = _ } ->
    let args = List.map ~f:(fun { binding = _; value } -> value) args in
    getIterationSpaceList (body :: args)
  | LoopBlock lb ->
    let size =
      match lb.frameShape with
      | Add { const; refs } ->
        if Map.is_empty refs then const else raise Unimplemented.default
      | ShapeRef _ -> raise Unimplemented.default
    in
    let mapBody = getIterationSpace lb.mapBody in
    let consumer = getIterationSpaceConsumer lb.consumer in
    (size * mapBody) + consumer
  | Box b -> getIterationSpace b.body
  | Values { elements; type' = _ } -> getIterationSpaceList elements
  | TupleDeref { tuple; index = _; type' = _ } -> getIterationSpace tuple
  | ContiguousSubArray
      { arrayArg; indexArg; originalShape = _; resultShape = _; type' = _ } ->
    getIterationSpaceList [ arrayArg; indexArg ]
  | Append { args; type' = _ } -> getIterationSpaceList args
  | Zip { zipArg; nestCount = _; type' = _ } -> getIterationSpace zipArg
  | Unzip { unzipArg; type' = _ } -> getIterationSpace unzipArg

and getIterationSpaceList (elements : Nested.t list) : int =
  List.fold elements ~init:0 ~f:(fun acc e -> acc + getIterationSpace e)

(* first is the constant 'cost', second is cost in loop*)
and getIterationSpaceConsumer consumer : int =
  let open Nested in
  let getSizeFromDim ({ const; refs } : Index.dimension) =
    if Map.is_empty refs then const else raise Unimplemented.default
  in
  match consumer with
  | None -> 0
  | Some (Reduce r) ->
    getIterationSpace r.zero + (getSizeFromDim r.d * getIterationSpace r.body)
  | Some (Fold f) ->
    getIterationSpace f.zeroArg.zeroValue + (getSizeFromDim f.d * getIterationSpace f.body)
  | Some (Scatter s) -> Int.max (getSizeFromDim s.dOut) (getSizeFromDim s.dIn)
;;

type parPath =
  { indexModeTree : IndexMode.index_tree_cuda_t
  ; inner : int
  ; extensible : bool
  }
[@@deriving sexp_of]

let rec findAllParOptions (expr : Nested.t) (structureMap : IndexMode.cuda_t)
  : Nested.t * parPath list
  =
  match expr with
  | Literal lit -> Literal lit, []
  | ScalarPrimitive prim -> ScalarPrimitive prim, []
  | Ref ref -> Ref ref, []
  | Frame { elements; dimension; type' } ->
    let elements, paths = findAllParOptionsList elements structureMap in
    Frame { elements; dimension; type' }, paths
  | BoxValue { box; type' } ->
    let newBox, paths = findAllParOptions box structureMap in
    BoxValue { box = newBox; type' }, paths
  | IndexLet { indexArgs; body; type' } ->
    let tArgs =
      List.map
        ~f:(fun { indexValue; indexBinding = _; sort = _ } ->
          match indexValue with
          | Runtime t -> t
          | FromBox { box; i = _ } -> box)
        indexArgs
    in
    let result, paths = findAllParOptionsList (body :: tArgs) structureMap in
    let newBody = List.hd_exn result in
    let newTArgs = List.tl_exn result in
    let newArgs =
      List.map2_exn
        indexArgs
        newTArgs
        ~f:(fun { indexValue; indexBinding; sort } newIndexValue ->
          let open Nested.Expr in
          let newIndexValue =
            match indexValue with
            | Runtime _ -> Runtime newIndexValue
            | FromBox { box = _; i } -> FromBox { box = newIndexValue; i }
          in
          { indexValue = newIndexValue; indexBinding; sort })
    in
    IndexLet { indexArgs = newArgs; body = newBody; type' }, paths
  | ReifyIndex ri -> ReifyIndex ri, []
  | ShapeProd sp -> ShapeProd sp, []
  | Let { args; body; type' } ->
    let argValues = List.map ~f:(fun { binding = _; value } -> value) args in
    let result, paths = findAllParOptionsList (body :: argValues) structureMap in
    let newBody = List.hd_exn result in
    let newArgsValues = List.tl_exn result in
    let newArgs =
      List.map2_exn args newArgsValues ~f:(fun { binding; value = _ } value ->
        Nested.Expr.{ binding; value })
    in
    Let { args = newArgs; body = newBody; type' }, paths
  | LoopBlock lb ->
    let _, innerPaths = findAllParOptions lb.mapBody structureMap in
    let innerIterSpaceMap = getIterationSpace lb.mapBody in
    let innerIterSpaceConsumer = getIterationSpaceConsumer lb.consumer in
    let innerIterSpace = innerIterSpaceConsumer + innerIterSpaceMap in
    let innerPaths =
      match innerPaths with
      | [] ->
        [ { indexModeTree = IndexMode.emptyIndexTree
          ; inner = innerIterSpace
          ; extensible = true
          }
        ]
      | innerPaths -> innerPaths
    in
    let newPossiblePaths =
      List.concat_map innerPaths ~f:(fun { indexModeTree; inner; extensible } ->
        let zeroPaths, bodyPaths = findAllParOptionsConsumer lb.consumer structureMap in
        let allConsumerPathsCombos = List.cartesian_product zeroPaths bodyPaths in
        let structureMap =
          IndexMode.updateStructureWithIndexModeTree structureMap indexModeTree
        in
        let loopBlockPar = IndexMode.tryToParallelizeCUDA structureMap lb in
        match loopBlockPar with
        | None ->
          (match lb.consumer with
           | None -> [ { indexModeTree; inner; extensible = false } ]
           | Some _ ->
             List.concat_map allConsumerPathsCombos ~f:(fun (a, b) ->
               let inner = innerIterSpaceMap + a.inner + b.inner in
               let indexModeTree =
                 IndexMode.branches [ indexModeTree; a.indexModeTree; b.indexModeTree ]
               in
               [ { indexModeTree; inner; extensible = false } ]))
        | Some loopBlockIndex ->
          let loopBlockIndex =
            IndexMode.createIndexModeAlloc ~label:lb.label ~indexMode:loopBlockIndex
          in
          if not extensible
          then (
            match lb.consumer with
            | None -> [ { indexModeTree; inner; extensible } ]
            | Some _ ->
              List.concat_map allConsumerPathsCombos ~f:(fun (a, b) ->
                let inner = innerIterSpaceMap + a.inner + b.inner in
                let indexModeTree =
                  IndexMode.branches [ indexModeTree; a.indexModeTree; b.indexModeTree ]
                in
                [ { indexModeTree; inner; extensible } ]))
          else if not (IndexMode.hasBeenParallelized indexModeTree)
          then (
            (* we haven't done par on this path *)
            let allocatedThisLoop =
              Option.value loopBlockIndex.indexMode.allocatedThreads ~default:1
              * Option.value loopBlockIndex.indexMode.allocatedBlocks ~default:1
            in
            let dontPar = { indexModeTree; inner = innerIterSpace; extensible } in
            let dontParWithParConsumer =
              List.concat_map allConsumerPathsCombos ~f:(fun (a, b) ->
                let inner = (innerIterSpaceMap * allocatedThisLoop) + a.inner + b.inner in
                let indexModeTree =
                  IndexMode.branches [ a.indexModeTree; b.indexModeTree ]
                in
                [ { indexModeTree; inner; extensible = false } ])
            in
            let extTreeOpt =
              IndexMode.appendIndexToTree [ loopBlockIndex ] indexModeTree
            in
            (* TODO: for the time being we only extend if there is no consumer *)
            let extExtensible = Option.is_none lb.consumer in
            match extTreeOpt with
            | None -> raise Unimplemented.default
            | Some tree ->
              let startPar =
                { indexModeTree = tree
                ; inner = innerIterSpace
                ; extensible = extExtensible
                }
              in
              let res = List.append [ dontPar; startPar ] dontParWithParConsumer in
              res)
          else (
            (* has been parallelized and extensible *)
            let extTreeOpt =
              IndexMode.appendIndexToTree [ loopBlockIndex ] indexModeTree
            in
            match extTreeOpt with
            | None -> raise Unimplemented.default
            | Some tree ->
              let continuePar =
                { indexModeTree = tree
                ; inner = inner + innerIterSpaceConsumer
                ; extensible
                }
              in
              (* TODO: i think this is redundant because of the first case but not fully sure *)
              let stopPar = { indexModeTree; inner; extensible = false } in
              let stopParWithParConsumer =
                List.concat_map allConsumerPathsCombos ~f:(fun (a, b) ->
                  let inner = inner + a.inner + b.inner in
                  let indexModeTree =
                    IndexMode.branches [ indexModeTree; a.indexModeTree; b.indexModeTree ]
                  in
                  [ { indexModeTree; inner; extensible = false } ])
              in
              List.append stopParWithParConsumer [ continuePar; stopPar ]))
    in
    LoopBlock lb, newPossiblePaths
  | Box { indices; body; bodyType; type' } ->
    let newBody, paths = findAllParOptions body structureMap in
    Box { body = newBody; indices; bodyType; type' }, paths
  | Values { elements; type' } ->
    let newElements, paths = findAllParOptionsList elements structureMap in
    Values { elements = newElements; type' }, paths
  | TupleDeref { tuple; index; type' } ->
    let newTuple, paths = findAllParOptions tuple structureMap in
    TupleDeref { tuple = newTuple; index; type' }, paths
  | ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' } ->
    let argResult, paths = findAllParOptionsList [ arrayArg; indexArg ] structureMap in
    let newArrayArg = List.nth_exn argResult 0 in
    let newIndexArg = List.nth_exn argResult 1 in
    ( ContiguousSubArray
        { arrayArg = newArrayArg
        ; indexArg = newIndexArg
        ; originalShape
        ; resultShape
        ; type'
        }
    , paths )
  | Append { args; type' } ->
    let newArgs, paths = findAllParOptionsList args structureMap in
    Append { args = newArgs; type' }, paths
  | Zip { zipArg; nestCount; type' } ->
    let newZipArg, paths = findAllParOptions zipArg structureMap in
    Zip { zipArg = newZipArg; nestCount; type' }, paths
  | Unzip { unzipArg; type' } ->
    let newUnzipArg, paths = findAllParOptions unzipArg structureMap in
    Unzip { unzipArg = newUnzipArg; type' }, paths

and findAllParOptionsList (elements : Nested.t list) (structureMap : IndexMode.cuda_t)
  : Nested.t list * parPath list
  =
  match elements with
  | [] -> elements, []
  | elements ->
    let allSegmentedPaths =
      List.map elements ~f:(fun e ->
        let e, paths = findAllParOptions e structureMap in
        e, paths)
    in
    let branchedApproach =
      List.filter_map allSegmentedPaths ~f:(fun (_, paths) ->
        if List.is_empty paths
        then None
        else (
          let bestPath =
            List.fold (List.tl_exn paths) ~init:(List.hd_exn paths) ~f:(fun best path ->
              let newBest =
                IndexMode.compareStructures
                  best.indexModeTree
                  path.indexModeTree
                  best.inner
                  path.inner
              in
              match newBest with
              | None -> best
              | Some newBest ->
                let newInner =
                  if IndexMode.equal_index_tree_cuda_t newBest best.indexModeTree
                  then best.inner
                  else path.inner
                in
                { indexModeTree = newBest; inner = newInner; extensible = false })
          in
          Some bestPath))
    in
    let allSegmentedPaths =
      List.map allSegmentedPaths ~f:(fun (e, paths) ->
        (* inner from all other elements since those won't get parallelized *)
        let otherInner =
          elements
          |> List.filter ~f:(fun e2 -> not (Nested.Expr.equal e2 e))
          |> List.fold ~init:0 ~f:(fun acc e -> acc + getIterationSpace e)
        in
        let paths =
          List.map paths ~f:(fun p -> { p with inner = p.inner + otherInner })
        in
        paths)
    in
    let branchPathTree =
      IndexMode.branches (List.map branchedApproach ~f:(fun b -> b.indexModeTree))
    in
    let branchTreeInner =
      List.fold branchedApproach ~init:0 ~f:(fun acc b -> acc + b.inner)
    in
    let branchExt =
      List.for_all branchedApproach ~f:(fun b ->
        not (IndexMode.hasBeenParallelized b.indexModeTree))
    in
    let branchPath =
      { indexModeTree = branchPathTree; inner = branchTreeInner; extensible = branchExt }
    in
    let allPaths = List.concat allSegmentedPaths in
    (* TODO: it might be worth to filter out some of the paths yet, but it seems like *)
    (*       performance is ok even without any filtering of branches *)
    elements, branchPath :: allPaths

and findAllParOptionsConsumer (consumer : Nested.Expr.consumerOp option) structureMap =
  match consumer with
  | None -> [], []
  | Some consumer ->
    (match consumer with
     | Nested.Expr.Reduce { arg = _; zero; body; d = _; character = _; type' = _ } ->
       let _, zeroPaths = findAllParOptionsList [ zero ] structureMap in
       let _, bodyPaths = findAllParOptionsList [ body ] structureMap in
       zeroPaths, bodyPaths
     | Nested.Expr.Fold
         { zeroArg; arrayArgs = _; body; reverse = _; d = _; character = _; type' = _ } ->
       let _, zeroPaths = findAllParOptionsList [ zeroArg.zeroValue ] structureMap in
       let _, bodyPaths = findAllParOptionsList [ body ] structureMap in
       zeroPaths, bodyPaths
     | Nested.Expr.Scatter _ -> [], [])
;;

let tableFromPath
  : IndexMode.index_tree_cuda_t -> (Identifier.t, IndexMode.index_cuda_t, _) Map.t
  =
  let rec tableFromPathHelper table
    : IndexMode.index_tree_cuda_t -> (Identifier.t, IndexMode.index_cuda_t, _) Map.t
    = function
    | FullPar allocTree ->
      List.fold allocTree ~init:table ~f:(fun table allocs ->
        List.fold allocs ~init:table ~f:(fun table { indexMode; loopBlockLabel } ->
          Map.set table ~key:loopBlockLabel ~data:indexMode))
    | Branches branches ->
      List.fold branches ~init:table ~f:(fun table b -> tableFromPathHelper table b)
  in
  tableFromPathHelper (Map.empty (module Identifier))
;;

let rec computeKernelSize
  (expr : Nested.t)
  (loopBlockParTable : (Identifier.t, IndexMode.index_cuda_t, _) Map.t)
  : int * int
  =
  let default = 1, 1 in
  match expr with
  | Ref _ -> default
  | Frame { dimension = _; elements; type' = _ } ->
    elements
    |> List.map ~f:(fun e -> computeKernelSize e loopBlockParTable)
    |> List.reduce ~f:(fun (b1, t1) (b2, t2) -> max b1 b2, max t1 t2)
    |> Option.value ~default
  | BoxValue { box; type' = _ } -> computeKernelSize box loopBlockParTable
  | IndexLet { indexArgs; body; type' = _ } ->
    let argsBlocks, argsThreads =
      indexArgs
      |> List.map ~f:(fun { indexBinding = _; indexValue; sort = _ } ->
        match indexValue with
        | Nested.Expr.Runtime v -> computeKernelSize v loopBlockParTable
        | Nested.Expr.FromBox { box; i = _ } -> computeKernelSize box loopBlockParTable)
      |> List.reduce ~f:(fun (b1, t1) (b2, t2) -> max b1 b2, max t1 t2)
      |> Option.value_exn
    in
    let bodyBlocks, bodyThreads = computeKernelSize body loopBlockParTable in
    max bodyBlocks argsBlocks, max bodyThreads argsThreads
  | ReifyIndex _ -> default
  | ShapeProd _ -> default
  | Let { args; body; type' = _ } ->
    let argsBlocks, argsThreads =
      args
      |> List.map ~f:(fun { binding = _; value } ->
        computeKernelSize value loopBlockParTable)
      |> List.reduce ~f:(fun (b1, t1) (b2, t2) -> max b1 b2, max t1 t2)
      |> Option.value ~default
    in
    let bodyBlocks, bodyThreads = computeKernelSize body loopBlockParTable in
    max argsBlocks bodyBlocks, max argsThreads bodyThreads
  | LoopBlock
      { label
      ; frameShape = _
      ; mapArgs = _
      ; mapIotas = _
      ; mapBody
      ; mapBodyMatcher = _
      ; mapResults = _
      ; consumer = _
      ; type' = _
      } ->
    let ((bodyBlocks, bodyThreads) as bodySize) =
      computeKernelSize mapBody loopBlockParTable
    in
    (match Map.find loopBlockParTable label with
     | None -> bodySize
     | Some { allocatedThreads; allocatedBlocks } ->
       (match allocatedBlocks, allocatedThreads with
        | None, None -> bodySize
        | Some blocks, None -> blocks * bodyBlocks, bodyThreads
        | None, Some threads -> bodyBlocks, threads * bodyThreads
        | Some blocks, Some threads -> bodyBlocks * blocks, bodyThreads * threads))
  | Box { indices = _; body; bodyType = _; type' = _ } ->
    computeKernelSize body loopBlockParTable
  | Literal _ -> default
  | Values { elements; type' = _ } ->
    elements
    |> List.map ~f:(fun e -> computeKernelSize e loopBlockParTable)
    |> List.reduce ~f:(fun (b1, t1) (b2, t2) -> max b1 b2, max t1 t2)
    |> Option.value ~default
  | ScalarPrimitive { op = _; args; type' = _ } ->
    args
    |> List.map ~f:(fun e -> computeKernelSize e loopBlockParTable)
    |> List.reduce ~f:(fun (b1, t1) (b2, t2) -> max b1 b2, max t1 t2)
    |> Option.value ~default
  | TupleDeref { index = _; tuple; type' = _ } ->
    computeKernelSize tuple loopBlockParTable
  | ContiguousSubArray
      { arrayArg; indexArg; originalShape = _; resultShape = _; type' = _ } ->
    let arrBlocks, arrThreads = computeKernelSize arrayArg loopBlockParTable in
    let idxBlocks, idxThreads = computeKernelSize indexArg loopBlockParTable in
    max arrBlocks idxBlocks, max arrThreads idxThreads
  | Append { args; type' = _ } ->
    args
    |> List.map ~f:(fun e -> computeKernelSize e loopBlockParTable)
    |> List.reduce ~f:(fun (b1, t1) (b2, t2) -> max b1 b2, max t1 t2)
    |> Option.value ~default
  | Zip { zipArg; nestCount = _; type' = _ } -> computeKernelSize zipArg loopBlockParTable
  | Unzip { unzipArg; type' = _ } -> computeKernelSize unzipArg loopBlockParTable
;;

let rec rewriteWithPar (expr : Nested.t) loopBlockParTable : Corn.t =
  let rec rewriteWithParHelper (expr : Nested.t) : Corn.t =
    match expr with
    | Ref { id; type' } -> Ref { id; type' }
    | Frame { dimension; elements; type' } ->
      let elements = List.map elements ~f:(fun e -> rewriteWithParHelper e) in
      Frame { dimension; elements; type' }
    | BoxValue { box; type' } ->
      let box = rewriteWithParHelper box in
      BoxValue { box; type' }
    | IndexLet { indexArgs; body; type' } ->
      let body = rewriteWithParHelper body in
      let convertIndexValue (indexValue : Nested.Expr.indexValue) : _ Corn.Expr.indexValue
        =
        match indexValue with
        | Runtime t -> Runtime (rewriteWithParHelper t)
        | FromBox { box; i } ->
          let box = rewriteWithParHelper box in
          FromBox { box; i }
      in
      let indexArgs =
        List.map
          indexArgs
          ~f:(fun { indexBinding; indexValue; sort } : _ Corn.Expr.indexArg ->
            let indexValue = convertIndexValue indexValue in
            { indexBinding; indexValue; sort })
      in
      IndexLet { indexArgs; body; type' }
    | ReifyIndex { index; type' } -> ReifyIndex { index; type' }
    | ShapeProd shape -> ShapeProd shape
    | Let { args; body; type' } ->
      let args =
        List.map args ~f:(fun { binding; value } : _ Corn.Expr.letArg ->
          let value = rewriteWithParHelper value in
          { binding; value })
      in
      let body = rewriteWithParHelper body in
      Let { args; body; type' }
    (* have to split loopBlocks like this because type system is being a bother *)
    | LoopBlock
        { label
        ; frameShape
        ; mapArgs
        ; mapIotas
        ; mapBody
        ; mapBodyMatcher
        ; mapResults
        ; consumer = None
        ; type'
        } as lb
      when Map.mem loopBlockParTable label ->
      let blocks, threads = computeKernelSize lb loopBlockParTable in
      let indexMode = Map.find loopBlockParTable label in
      let mapBody = exprToMapBody mapBody loopBlockParTable in
      let type' = List.nth_exn type' 0 in
      let lb : Corn.Expr.mapKernel =
        { indexMode
        ; frameShape
        ; mapArgs
        ; mapIotas
        ; mapBody
        ; mapBodyMatcher
        ; mapResults
        ; type'
        }
      in
      let kernel = Corn.Expr.{ kernel = lb; blocks; threads } in
      Corn.Expr.values [ Corn.Expr.MapKernel kernel; Corn.Expr.values [] ]
    | LoopBlock
        { label
        ; frameShape
        ; mapArgs
        ; mapIotas
        ; mapBody
        ; mapBodyMatcher
        ; mapResults
        ; consumer = Some consumer
        ; type'
        } as lb
      when Map.mem loopBlockParTable label ->
      let blocks, threads = computeKernelSize lb loopBlockParTable in
      let indexMode = Map.find loopBlockParTable label in
      let mapBody = rewriteWithParDevice mapBody loopBlockParTable in
      let consumer =
        rewriteWithParConsumerHostDevicePar consumer indexMode loopBlockParTable
      in
      let consumer = Maybe.Just consumer in
      let lb : (host, device, Corn.Expr.parallel, _) Corn.Expr.loopBlock =
        { indexMode
        ; frameShape
        ; mapArgs
        ; mapIotas
        ; mapBody
        ; mapBodyMatcher
        ; mapResults
        ; consumer
        ; type'
        }
      in
      let kernel = Corn.Expr.{ kernel = lb; blocks; threads } in
      Corn.Expr.LoopKernel kernel
    (* this is host sequential *)
    | LoopBlock
        { label = _
        ; frameShape
        ; mapArgs
        ; mapIotas
        ; mapBody
        ; mapBodyMatcher
        ; mapResults
        ; consumer = None
        ; type'
        } ->
      let mapBody = rewriteWithParHelper mapBody in
      Corn.Expr.LoopBlock
        { indexMode = None (* we would go to branch above otherwise *)
        ; frameShape
        ; mapArgs
        ; mapIotas
        ; mapBody
        ; mapBodyMatcher
        ; mapResults
        ; consumer = Maybe.Nothing
        ; type'
        }
    | LoopBlock
        { label = _
        ; frameShape
        ; mapArgs
        ; mapIotas
        ; mapBody
        ; mapBodyMatcher
        ; mapResults
        ; consumer = Some consumer
        ; type'
        } ->
      let mapBody = rewriteWithParHelper mapBody in
      let consumer = Maybe.Just (rewriteWithParConsumerHost consumer) in
      Corn.Expr.LoopBlock
        { indexMode = None (* we would go to branch above otherwise *)
        ; frameShape
        ; mapArgs
        ; mapIotas
        ; mapBody
        ; mapBodyMatcher
        ; mapResults
        ; consumer
        ; type'
        }
    | Box { indices; body; bodyType; type' } ->
      let body = rewriteWithParHelper body in
      Box { indices; body; bodyType; type' }
    | Literal lit -> Literal lit
    | Values { elements; type' } ->
      let elements = List.map elements ~f:rewriteWithParHelper in
      Values { elements; type' }
    | ScalarPrimitive { op; args; type' } ->
      let args = List.map args ~f:rewriteWithParHelper in
      ScalarPrimitive { op; args; type' }
    | TupleDeref { index; tuple; type' } ->
      let tuple = rewriteWithParHelper tuple in
      (match tuple with
       | Values { elements; type' = _ } -> List.nth_exn elements index
       | tuple -> TupleDeref { index; tuple; type' })
    | ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' } ->
      let arrayArg = rewriteWithParHelper arrayArg in
      let indexArg = rewriteWithParHelper indexArg in
      ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' }
    | Append { args; type' } ->
      let args = List.map args ~f:rewriteWithParHelper in
      Append { args; type' }
    | Zip { zipArg; nestCount; type' } ->
      let zipArg = rewriteWithParHelper zipArg in
      Zip { zipArg; nestCount; type' }
    | Unzip { unzipArg; type' } ->
      let unzipArg = rewriteWithParHelper unzipArg in
      Unzip { unzipArg; type' }
  and rewriteWithParConsumerHost (consumer : Nested.Expr.consumerOp) =
    match consumer with
    | Reduce { arg; zero; body; d; character; type' } ->
      let zero = rewriteWithParHelper zero in
      let body = rewriteWithParHelper body in
      let reduceLike : (host, host) Corn.Expr.reduceLike =
        { arg; body; zero; indexMode = None; d; type' }
      in
      (match character with
       | Reduce -> ReduceSeq reduceLike
       | Scan -> ScanSeq reduceLike)
    | Fold
        { zeroArg = { zeroBinding; zeroValue }
        ; arrayArgs
        ; body
        ; reverse
        ; d
        ; character
        ; type'
        } ->
      let zeroArg =
        Corn.Expr.{ zeroBinding; zeroValue = rewriteWithParHelper zeroValue }
      in
      let body = rewriteWithParHelper body in
      Fold { zeroArg; arrayArgs; body; reverse; d; character; type' }
    | Scatter { valuesArg; indicesArg; dIn; dOut; type' } ->
      Scatter { valuesArg; indicesArg; dIn; dOut; type' }
  in
  rewriteWithParHelper expr

and rewriteWithParDevice (expr : Nested.t) loopBlockParTable =
  match expr with
  | LoopBlock
      { frameShape
      ; label
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer = None
      ; type'
      }
    when Map.mem loopBlockParTable label ->
    let indexMode = Map.find_exn loopBlockParTable label in
    let mapBody = rewriteWithParDevice mapBody loopBlockParTable in
    let loopBlock : (device, device, Corn.Expr.parallel, _) Corn.Expr.loopBlock =
      { frameShape
      ; indexMode = Some indexMode
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer = Maybe.Nothing
      ; type'
      }
    in
    LoopBlock loopBlock
  | LoopBlock
      { frameShape
      ; label
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer = Some consumer
      ; type'
      }
    when Map.mem loopBlockParTable label ->
    let indexMode = Map.find loopBlockParTable label in
    let mapBody = rewriteWithParDevice mapBody loopBlockParTable in
    let consumer = rewriteWithParConsumerDevicePar consumer indexMode loopBlockParTable in
    let consumer = Maybe.Just consumer in
    let loopBlock : (device, device, Corn.Expr.parallel, _) Corn.Expr.loopBlock =
      { frameShape
      ; indexMode
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer
      ; type'
      }
    in
    LoopBlock loopBlock
  | LoopBlock
      { frameShape
      ; label
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer = None
      ; type'
      } ->
    (* otherwise we are sequential *)
    let open Corn in
    let indexMode = Map.find loopBlockParTable label in
    let mapBody = rewriteWithParDevice mapBody loopBlockParTable in
    let consumer = Maybe.Nothing in
    let loopBlock : (device, device, Expr.sequential, _) Corn.Expr.loopBlock =
      { frameShape
      ; indexMode
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer
      ; type'
      }
    in
    LoopBlock loopBlock
  | LoopBlock
      { frameShape
      ; label
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer = Some consumer
      ; type'
      } ->
    (* otherwise we are sequential *)
    let open Corn in
    let indexMode = Map.find loopBlockParTable label in
    let mapBody = rewriteWithParDevice mapBody loopBlockParTable in
    let consumer : (_, _, Expr.sequential) Expr.consumerOp =
      rewriteWithParConsumerDeviceSeq consumer indexMode loopBlockParTable
    in
    let consumer = Maybe.Just consumer in
    let type' = type' in
    let loopBlock : (device, device, Expr.sequential, _) Corn.Expr.loopBlock =
      { frameShape
      ; indexMode
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer
      ; type'
      }
    in
    LoopBlock loopBlock
  | Frame { dimension; elements; type' } ->
    let elements =
      List.map elements ~f:(fun e -> rewriteWithParDevice e loopBlockParTable)
    in
    Frame { elements; dimension; type' }
  | Ref r -> Ref r
  | BoxValue { box; type' } ->
    let box = rewriteWithParDevice box loopBlockParTable in
    BoxValue { box; type' }
  | IndexLet { indexArgs; body; type' } ->
    let indexArgs =
      indexArgs
      |> List.map ~f:(fun { indexBinding; indexValue; sort } ->
        let indexValue : _ Corn.Expr.indexValue =
          match indexValue with
          | Nested.Expr.Runtime v -> Runtime (rewriteWithParDevice v loopBlockParTable)
          | Nested.Expr.FromBox { box; i } ->
            let box = rewriteWithParDevice box loopBlockParTable in
            FromBox { box; i }
        in
        Corn.Expr.{ indexBinding; indexValue; sort })
    in
    let body = rewriteWithParDevice body loopBlockParTable in
    IndexLet { indexArgs; body; type' }
  | ReifyIndex r -> ReifyIndex r
  | ShapeProd shape -> ShapeProd shape
  | Let { args; body; type' } ->
    let args =
      List.map args ~f:(fun { binding; value } ->
        let value = rewriteWithParDevice value loopBlockParTable in
        Corn.Expr.{ binding; value })
    in
    let body = rewriteWithParDevice body loopBlockParTable in
    Let { args; body; type' }
  | Box { indices; body; bodyType; type' } ->
    let body = rewriteWithParDevice body loopBlockParTable in
    Box { indices; body; bodyType; type' }
  | Literal l -> Literal l
  | Values { elements; type' } ->
    let elements =
      List.map elements ~f:(fun e -> rewriteWithParDevice e loopBlockParTable)
    in
    Values { elements; type' }
  | ScalarPrimitive { op; args; type' } ->
    let args = List.map args ~f:(fun a -> rewriteWithParDevice a loopBlockParTable) in
    ScalarPrimitive { op; args; type' }
  | TupleDeref { index; tuple; type' } ->
    let tuple = rewriteWithParDevice tuple loopBlockParTable in
    TupleDeref { index; tuple; type' }
  | ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' } ->
    let arrayArg = rewriteWithParDevice arrayArg loopBlockParTable in
    let indexArg = rewriteWithParDevice indexArg loopBlockParTable in
    ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' }
  | Append { args; type' } ->
    let args = List.map args ~f:(fun a -> rewriteWithParDevice a loopBlockParTable) in
    Append { args; type' }
  | Zip { zipArg; nestCount; type' } ->
    let zipArg = rewriteWithParDevice zipArg loopBlockParTable in
    Zip { zipArg; nestCount; type' }
  | Unzip { unzipArg; type' } ->
    let unzipArg = rewriteWithParDevice unzipArg loopBlockParTable in
    Unzip { unzipArg; type' }

and rewriteWithParConsumerDevicePar
  (consumer : Nested.Expr.consumerOp)
  indexMode
  loopBlockParTable
  : (device, device, Corn.Expr.parallel) Corn.Expr.consumerOp
  =
  match consumer with
  | Reduce { arg; zero; body; d; character; type' } ->
    let zero = rewriteWithParDevice zero loopBlockParTable in
    let body = rewriteWithParDevice body loopBlockParTable in
    let reduceLike : (device, device) Corn.Expr.reduceLike =
      { arg; zero; body; indexMode; d; type' }
    in
    (match character with
     | Reduce ->
       raise
         (Unimplemented.Error
            "Currently no par reduce inside a kernel, only on the boundary")
     | Scan -> ScanPar reduceLike)
  | Fold
      { zeroArg = _
      ; arrayArgs = _
      ; body = _
      ; reverse = _
      ; d = _
      ; character = _
      ; type' = _
      } -> raise Unimplemented.default (* fold is sequential so cannot be parallelized *)
  | Scatter { valuesArg; indicesArg; dIn; dOut; type' } ->
    Scatter { valuesArg; indicesArg; dIn; dOut; type' }

and rewriteWithParConsumerDeviceSeq
  (consumer : Nested.Expr.consumerOp)
  indexMode
  loopBlockParTable
  : (device, device, Corn.Expr.sequential) Corn.Expr.consumerOp
  =
  match consumer with
  | Reduce { arg; zero; body; d; character; type' } ->
    let zero = rewriteWithParDevice zero loopBlockParTable in
    let body = rewriteWithParDevice body loopBlockParTable in
    let reduceLike : (device, device) Corn.Expr.reduceLike =
      { arg; zero; body; indexMode; d; type' }
    in
    (match character with
     | Reduce -> ReduceSeq reduceLike
     | Scan -> ScanSeq reduceLike)
  | Fold
      { zeroArg = { zeroBinding; zeroValue }
      ; arrayArgs
      ; body
      ; reverse
      ; d
      ; character
      ; type'
      } ->
    let zeroValue = rewriteWithParDevice zeroValue loopBlockParTable in
    let zeroArg : _ Corn.Expr.foldZeroArg = { zeroBinding; zeroValue } in
    let body = rewriteWithParDevice body loopBlockParTable in
    Fold { zeroArg; arrayArgs; body; reverse; d; character; type' }
  | Scatter { valuesArg; indicesArg; dIn; dOut; type' } ->
    Scatter { valuesArg; indicesArg; dIn; dOut; type' }

and rewriteWithParConsumerHostDevicePar consumer indexMode loopBlockParTable
  : (host, device, Corn.Expr.parallel) Corn.Expr.consumerOp
  =
  match consumer with
  | Reduce { arg; zero; body; d; character; type' } ->
    let zero = rewriteWithPar zero loopBlockParTable in
    let outerBody : host Corn.Expr.t = rewriteWithPar body loopBlockParTable in
    let body = rewriteWithParDevice body loopBlockParTable in
    let reduceLike : (host, device) Corn.Expr.reduceLike =
      { arg; zero; body; indexMode; d; type' }
    in
    (match character with
     | Reduce -> ReducePar { reduce = reduceLike; outerBody }
     | Scan -> ScanPar reduceLike)
  | Fold
      { zeroArg = _
      ; arrayArgs = _
      ; body = _
      ; reverse = _
      ; d = _
      ; character = _
      ; type' = _
      } -> raise Unimplemented.default (* fold is sequential so cannot be parallelized *)
  | Scatter { valuesArg; indicesArg; dIn; dOut; type' } ->
    Scatter { valuesArg; indicesArg; dIn; dOut; type' }

and exprToMapBody (expr : Nested.t) loopBlockParTable =
  match expr with
  | (TupleDeref _ | Values _ | LoopBlock _) as expr ->
    let possibleSubMap = exprToMapBodySubMap expr loopBlockParTable in
    (match possibleSubMap with
     | None -> MapBodyExpr (rewriteWithParDevice expr loopBlockParTable)
     | Some subMap -> MapBodySubMap subMap)
  | rest -> MapBodyExpr (rewriteWithParDevice rest loopBlockParTable)

and exprToMapBodySubMap (expr : Nested.t) loopBlockParTable
  : Corn.Expr.mapBodySubMap option
  =
  match expr with
  | LoopBlock
      { frameShape
      ; label
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer = None
      ; type'
      } ->
    let indexMode = Map.find loopBlockParTable label in
    let mapBody = exprToMapBody mapBody loopBlockParTable in
    let type' = Type.Tuple type' in
    let mapKernel : Corn.Expr.mapKernel =
      { frameShape
      ; indexMode
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; type'
      }
    in
    Some (MapBodyMap mapKernel)
  | TupleDeref { index; tuple; type' = _ } ->
    let tuple = exprToMapBodySubMap tuple loopBlockParTable in
    (match tuple with
     | None -> None
     | Some tuple -> Some (MapBodyDeref { index; tuple }))
  | Values { elements; type' = _ } ->
    let elements =
      elements |> List.map ~f:(fun e -> exprToMapBodySubMap e loopBlockParTable)
    in
    let allGood = List.for_all elements ~f:Option.is_some in
    if allGood
    then Some (MapBodyValues (List.map elements ~f:(fun e -> Option.value_exn e)))
    else None
  | _ -> None
;;

let kernelize (expr : Nested.t) : (CompilerState.state, Corn.t, _) State.t =
  Stdio.prerr_endline "Fuse and Simplify done";
  (* This stage consists of 2 steps: collect possible paths and rewrite the program using the best one *)
  let _, paths = findAllParOptions expr IndexMode.defaultCUDA in
  let bestPath =
    match paths with
    | [] -> raise Unimplemented.default
    | hd :: tl ->
      List.fold tl ~init:hd ~f:(fun best path ->
        let newBest =
          IndexMode.compareStructures
            best.indexModeTree
            path.indexModeTree
            best.inner
            path.inner
        in
        match newBest with
        | None -> best
        | Some newBest ->
          let newInner =
            if IndexMode.equal_index_tree_cuda_t newBest best.indexModeTree
            then best.inner
            else path.inner
          in
          { indexModeTree = newBest; inner = newInner; extensible = false })
  in
  (* paths *)
  (* |> [%sexp_of: parPath list] *)
  (* |> Sexp.to_string_hum *)
  (* |> Printf.sprintf "Resulting indices: %s" *)
  (* |> Stdio.print_endline; *)
  (* bestPath *)
  (* |> [%sexp_of: parPath] *)
  (* |> Sexp.to_string_hum *)
  (* |> Printf.sprintf "Best path %s" *)
  (* |> Stdio.print_endline; *)
  let loopBlockParTable = tableFromPath bestPath.indexModeTree in
  let newExpr : Corn.t = rewriteWithPar expr loopBlockParTable in
  Stdio.prerr_endline "Kernelize done";
  State.return newExpr
;;

module Stage (SB : Source.BuilderT) = struct
  type state = CompilerState.state
  type input = Nested.t
  type output = Corn.t
  type error = (SB.source option, string) Source.annotate

  let name = "Kernelize"

  let run input =
    CompilerPipeline.S.make ~f:(fun state -> State.run (kernelize input) state)
  ;;
end
