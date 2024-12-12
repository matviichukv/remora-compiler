open! Core
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

type iterSpace = IndexMode.iterSpace [@@deriving sexp_of]

(* let rec getIterationSpace (expr : Nested.t) : iterSpace = *)
(*   match expr with *)
(*   | Literal _ -> 1 *)
(*   | ScalarPrimitive _ -> 1 *)
(*   | Ref _ -> 1 *)
(*   | Frame { elements; dimension = _; type' = _ } -> getIterationSpaceList elements *)
(*   | BoxValue bv -> getIterationSpace bv.box *)
(*   | IndexLet { indexArgs; body; type' = _ } -> *)
(*     let tArgs = *)
(*       List.map *)
(*         ~f:(fun { indexValue; indexBinding = _; sort = _ } -> *)
(*           match indexValue with *)
(*           | Runtime t -> t *)
(*           | FromBox { box; i = _ } -> box) *)
(*         indexArgs *)
(*     in *)
(*     getIterationSpaceList (body :: tArgs) *)
(*   | ReifyIndex _ -> 1 *)
(*   | ShapeProd _ -> 1 *)
(*   | Let { args; body; type' = _ } -> *)
(*     let args = List.map ~f:(fun { binding = _; value } -> value) args in *)
(*     getIterationSpaceList (body :: args) *)
(*   | LoopBlock lb -> *)
(*     let size = *)
(*       match lb.frameShape with *)
(*       | Add { const; refs } -> *)
(*         if Map.is_empty refs then const else raise Unimplemented.default *)
(*       | ShapeRef _ -> raise Unimplemented.default *)
(*     in *)
(*     let mapBody = getIterationSpace lb.mapBody in *)
(*     let consumer = getIterationSpaceConsumer lb.consumer in *)
(*     (size * mapBody) + consumer *)
(*   | Box b -> getIterationSpace b.body *)
(*   | Values { elements; type' = _ } -> getIterationSpaceList elements *)
(*   | TupleDeref { tuple; index = _; type' = _ } -> getIterationSpace tuple *)
(*   | ContiguousSubArray *)
(*       { arrayArg; indexArg; originalShape = _; resultShape = _; type' = _ } -> *)
(*     getIterationSpaceList [ arrayArg; indexArg ] *)
(*   | Append { args; type' = _ } -> getIterationSpaceList args *)
(*   | Zip { zipArg; nestCount = _; type' = _ } -> getIterationSpace zipArg *)
(*   | Unzip { unzipArg; type' = _ } -> getIterationSpace unzipArg *)

(* and getIterationSpaceList (elements : Nested.t list) : iterSpace = *)
(*   List.fold elements ~init:0 ~f:(fun acc e -> acc + getIterationSpace e) *)

(* (\* first is the constant 'cost', second is cost in loop*\) *)
(* and getIterationSpaceConsumer consumer : iterSpace = *)
(*   let open Nested in *)
(*   let getSizeFromDim ({ const; refs } : Index.dimension) = *)
(*     if Map.is_empty refs then const else raise Unimplemented.default *)
(*   in *)
(*   match consumer with *)
(*   | None -> 0 *)
(*   | Some (Reduce r) -> getIterationSpace r.zero + getIterationSpace r.body *)
(*   | Some (Fold f) -> getIterationSpace f.zeroArg.zeroValue + getIterationSpace f.body *)
(*   | Some (Scatter s) -> Int.max (getSizeFromDim s.dOut) (getSizeFromDim s.dIn) *)
(* ;; *)

type parPath =
  { indexModeTree : IndexMode.index_tree_cuda_t
  ; inner : iterSpace
  ; extensible : bool
  }
[@@deriving sexp_of]

let rec findAllParOptions (expr : Nested.t) (structureMap : IndexMode.cuda_t)
  : Nested.t * parPath list
  =
  match expr with
  | Literal lit -> Literal lit, []
  | ScalarPrimitive { op; args; type' } ->
    let _, paths = findAllParOptionsList args structureMap in
    ScalarPrimitive { op; args; type' }, paths
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
    (* let innerIterSpaceMap = getIterationSpace lb.mapBody in *)
    (* let innerIterSpaceConsumer = getIterationSpaceConsumer lb.consumer in *)
    (* let innerIterSpace = innerIterSpaceConsumer + innerIterSpaceMap in *)
    let innerIterSpaceMap = IndexMode.exprIterSpace lb.mapBody in
    let innerIterSpaceConsumer, innerIterSpaceZero =
      lb.consumer
      |> Option.map ~f:IndexMode.consumerIterSpace
      |> Option.value ~default:(IndexMode.constantIterSpace, IndexMode.constantIterSpace)
    in
    let innerIterSpace =
      IndexMode.addIterSpaces innerIterSpaceMap innerIterSpaceConsumer
    in
    let innerIterSpace = IndexMode.addIterSpaces innerIterSpace innerIterSpaceZero in
    let innerPaths =
      match innerPaths with
      | [] ->
        [ { indexModeTree = IndexMode.emptyIndexTree
          ; inner = IndexMode.constantIterSpace
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
               let inner =
                 IndexMode.addIterSpaces
                   innerIterSpaceMap
                   (IndexMode.addIterSpaces a.inner b.inner)
               in
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
            | None ->
              (* [ { indexModeTree; inner; extensible } ] *)
              if IndexMode.isViableKernel indexModeTree
              then [ { indexModeTree; inner; extensible } ]
              else []
            | Some _ ->
              List.concat_map allConsumerPathsCombos ~f:(fun (a, b) ->
                let inner =
                  IndexMode.addIterSpaces
                    innerIterSpaceMap
                    (IndexMode.addIterSpaces a.inner b.inner)
                in
                let indexModeTree =
                  IndexMode.branches [ indexModeTree; a.indexModeTree; b.indexModeTree ]
                in
                [ { indexModeTree; inner; extensible } ]))
          else if not (IndexMode.hasBeenParallelized indexModeTree)
          then (
            (* we haven't done par on this path *)
            (* let allocatedThisLoop = *)
            (*   (\* multiply *\) *)
            (*   (Option.value loopBlockIndex.indexMode.allocatedThreads ~default:(Static 1)) *)
            (*     (Option.value *)
            (*        loopBlockIndex.indexMode.allocatedBlocks *)
            (*        ~default:(Static 1)) *)
            (* in *)
            let dontPar = { indexModeTree; inner = innerIterSpace; extensible } in
            let dontParWithParConsumer =
              List.concat_map allConsumerPathsCombos ~f:(fun (a, b) ->
                let inner =
                  IndexMode.addIterSpaces
                    (IndexMode.iterSpaceMultDim innerIterSpaceMap lb.frameShape)
                    (IndexMode.addIterSpaces a.inner b.inner)
                in
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
                ; inner = IndexMode.addIterSpaces inner innerIterSpaceConsumer
                ; extensible
                }
              in
              (* TODO: i think this is redundant because of the first case but not fully sure *)
              let stopPar = { indexModeTree; inner; extensible = false } in
              let stopParWithParConsumer =
                List.concat_map allConsumerPathsCombos ~f:(fun (a, b) ->
                  let inner =
                    IndexMode.addIterSpaces
                      inner
                      (IndexMode.addIterSpaces a.inner b.inner)
                  in
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
        let paths =
          List.filter paths ~f:(fun a ->
            a.extensible || IndexMode.isViableKernel a.indexModeTree)
        in
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
          |> List.fold ~init:IndexMode.zeroIterSpace ~f:(fun acc e ->
            IndexMode.addIterSpaces acc (IndexMode.exprIterSpace e))
        in
        let paths =
          List.map paths ~f:(fun p ->
            { p with inner = IndexMode.addIterSpaces p.inner otherInner })
        in
        paths)
    in
    let branchPathTree =
      IndexMode.branches (List.map branchedApproach ~f:(fun b -> b.indexModeTree))
    in
    let branchTreeInner =
      List.fold branchedApproach ~init:IndexMode.zeroIterSpace ~f:(fun acc b ->
        IndexMode.addIterSpaces acc b.inner)
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

let convertScalarOp (op : Nested.Expr.scalarOp) : Corn.Expr.scalarOp =
  match op with
  | Add -> Add
  | Sub -> Sub
  | Mul -> Mul
  | Div -> Div
  | Mod -> Mod
  | AddF -> AddF
  | SubF -> SubF
  | MulF -> MulF
  | DivF -> DivF
  | IntToBool -> IntToBool
  | BoolToInt -> BoolToInt
  | IntToFloat -> IntToFloat
  | FloatToInt -> FloatToInt
  | Equal -> Equal
  | EqualF -> EqualF
  | Ne -> Ne
  | Gt -> Gt
  | GtEq -> GtEq
  | Lt -> Lt
  | LtEq -> LtEq
  | GtF -> GtF
  | GtEqF -> GtEqF
  | LtF -> LtF
  | LtEqF -> LtEqF
  | And -> And
  | Or -> Or
  | Not -> Not
  | If -> If
  | LibFun { name; libName; argTypes; retType } ->
    LibFun { name; libName; argTypes; retType }
  | IOFun { name; libName; libTypeParams; argTypes; retType } ->
    IOFun { name; libName; libTypeParams; argTypes; retType }
;;

type kernelParallelism =
  { parBlocks : Corn.Expr.parallelism
  ; parThreads : Corn.Expr.parallelism
  }

let unitKernelPar =
  [ { parBlocks = KnownParallelism 1; parThreads = KnownParallelism 1 } ]
;;

let addIndexModeToPar (indexMode : IndexMode.index_cuda_t) par =
  match indexMode.allocatedThreads, indexMode.allocatedBlocks with
  | Some allocatedThreads, Some allocatedBlocks ->
    let shapeBlocks =
      match allocatedBlocks with
      | Nested.Expr.Static n ->
        Corn.Index.Add { refs = Map.empty (module Identifier); const = n }
      | Nested.Expr.Dynamic d -> d
    in
    let shapeThreads =
      match allocatedThreads with
      | Nested.Expr.Static n ->
        Corn.Index.Add { refs = Map.empty (module Identifier); const = n }
      | Nested.Expr.Dynamic d -> d
    in
    { parThreads = Parallelism { shape = shapeThreads; rest = par.parThreads }
    ; parBlocks = Parallelism { shape = shapeBlocks; rest = par.parBlocks }
    }
  | None, Some allocatedBlocks ->
    let shape =
      match allocatedBlocks with
      | Nested.Expr.Static n ->
        Corn.Index.Add { refs = Map.empty (module Identifier); const = n }
      | Nested.Expr.Dynamic d -> d
    in
    { par with parBlocks = Parallelism { shape; rest = par.parBlocks } }
  | Some allocatedThreads, None ->
    let shape =
      match allocatedThreads with
      | Nested.Expr.Static n ->
        Corn.Index.Add { refs = Map.empty (module Identifier); const = n }
      | Nested.Expr.Dynamic d -> d
    in
    { par with parThreads = Parallelism { shape; rest = par.parThreads } }
  | None, None -> par
;;

let rec collectParallelism loopBlockParTable (expr : Nested.t) : kernelParallelism list =
  match expr with
  | Ref _ -> unitKernelPar
  | Frame _ -> unitKernelPar
  | BoxValue { box; type' = _ } -> collectParallelism loopBlockParTable box
  | IndexLet { indexArgs = _; body; type' = _ } ->
    collectParallelism loopBlockParTable body
  | ReifyIndex _ -> unitKernelPar
  | ShapeProd _ -> unitKernelPar
  | Let { args; body; type' = _ } ->
    let argVals = List.map args ~f:(fun a -> a.value) in
    List.concat_map (body :: argVals) ~f:(collectParallelism loopBlockParTable)
  | LoopBlock
      { label
      ; frameShape = _
      ; mapArgs = _
      ; mapIotas = _
      ; mapBody
      ; mapBodyMatcher = _
      ; mapResults = _
      ; consumer
      ; type' = _
      } ->
    let consumerPar =
      Option.map consumer ~f:(collectParallelismConsumer loopBlockParTable)
    in
    let bodyPar = collectParallelism loopBlockParTable mapBody in
    (match consumerPar with
     | None when Map.mem loopBlockParTable label ->
       let indexMode : IndexMode.index_cuda_t = Map.find_exn loopBlockParTable label in
       List.map bodyPar ~f:(fun p -> addIndexModeToPar indexMode p)
     | None -> collectParallelism loopBlockParTable mapBody
     | Some (consumerBodyPar, consumerZeroPar) ->
       (* let innerPar : Corn.Expr.parallelism = *)
       (*   MaxParallelism [ bodyPar; consumerBodyPar ] *)
       (* in *)
       let innerPar = List.append bodyPar consumerBodyPar in
       let loopPar =
         if Map.mem loopBlockParTable label
         then (
           let indexMode : IndexMode.index_cuda_t =
             Map.find_exn loopBlockParTable label
           in
           List.map innerPar ~f:(fun p -> addIndexModeToPar indexMode p))
         else innerPar
       in
       List.append loopPar consumerZeroPar)
  | Box { indices = _; body; bodyType = _; type' = _ } ->
    collectParallelism loopBlockParTable body
  | Literal _ -> unitKernelPar
  | Values { elements; type' = _ } ->
    List.concat_map elements ~f:(collectParallelism loopBlockParTable)
  | ScalarPrimitive { op = _; args; type' = _ } ->
    List.concat_map args ~f:(collectParallelism loopBlockParTable)
  | TupleDeref { index = _; tuple; type' = _ } ->
    collectParallelism loopBlockParTable tuple
  | ContiguousSubArray
      { arrayArg; indexArg; originalShape = _; resultShape = _; type' = _ } ->
    List.concat_map [ arrayArg; indexArg ] ~f:(collectParallelism loopBlockParTable)
  | Append { args; type' = _ } ->
    List.concat_map args ~f:(collectParallelism loopBlockParTable)
  | Zip { zipArg; nestCount = _; type' = _ } ->
    collectParallelism loopBlockParTable zipArg
  | Unzip { unzipArg; type' = _ } -> collectParallelism loopBlockParTable unzipArg

(* returns two parallelisms, left is for body of the consumer *)
(* right one for the possible zero element *)
and collectParallelismConsumer loopBlockParTable (consumer : Nested.Expr.consumerOp)
  : kernelParallelism list * kernelParallelism list
  =
  match consumer with
  | Nested.Expr.Reduce { arg = _; zero; body; d = _; character = _; type' = _ } ->
    collectParallelism loopBlockParTable body, collectParallelism loopBlockParTable zero
  | Nested.Expr.Fold
      { zeroArg; arrayArgs = _; body; reverse = _; d = _; character = _; type' = _ } ->
    ( collectParallelism loopBlockParTable body
    , collectParallelism loopBlockParTable zeroArg.zeroValue )
  | Nested.Expr.Scatter _ -> unitKernelPar, unitKernelPar
;;

let rec partialEvalParallelism (p : Corn.Expr.parallelism) : Corn.Expr.parallelism =
  match (p : Corn.Expr.parallelism) with
  | KnownParallelism i -> KnownParallelism i
  | Parallelism { shape; rest } ->
    let rest = partialEvalParallelism rest in
    (match shape with
     | Index.Add { const; refs } when Map.is_empty refs ->
       (match rest with
        | KnownParallelism i -> KnownParallelism (i * const)
        | rest -> Parallelism { shape; rest })
     | _ -> Parallelism { shape; rest })
  | MaxParallelism pars ->
    let pars = List.map pars ~f:partialEvalParallelism in
    let known, unknown =
      List.partition_tf pars ~f:(function
        | KnownParallelism _ -> true
        | _ -> false)
    in
    let known =
      List.reduce known ~f:(fun a b ->
        match a, b with
        | KnownParallelism a, KnownParallelism b -> KnownParallelism (Int.max a b)
        | _, _ -> raise Unreachable.default)
    in
    let known = known |> Option.map ~f:List.singleton |> Option.value ~default:[] in
    (match known, unknown with
     | [ p ], [] -> p
     | known, unknown -> MaxParallelism (List.append known unknown))
;;

let rec combinePars (p1 : Corn.Expr.parallelism) (p2 : Corn.Expr.parallelism)
  : Corn.Expr.parallelism
  =
  match p1 with
  | Corn.Expr.KnownParallelism n ->
    Parallelism
      { shape = Add { const = n; refs = Map.empty (module Identifier) }; rest = p2 }
  | Corn.Expr.Parallelism { shape; rest } ->
    combinePars rest (Parallelism { shape; rest = p2 })
  | Corn.Expr.MaxParallelism pars ->
    MaxParallelism (List.map pars ~f:(fun p -> combinePars p p2))
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
      (* the sequential version of the loopBlock *)
      let init = rewriteWithPar lb (Map.empty (module Identifier)) in
      let parallelismList = collectParallelism loopBlockParTable lb in
      let parallelismList =
        List.map parallelismList ~f:(fun { parBlocks; parThreads } ->
          let parBlocks = partialEvalParallelism parBlocks in
          let parThreads = partialEvalParallelism parThreads in
          { parBlocks; parThreads })
      in
      let parBlocks =
        List.map ~f:(fun p -> p.parBlocks) parallelismList
        |> MaxParallelism
        |> partialEvalParallelism
      in
      let parThreads =
        List.map ~f:(fun p -> p.parThreads) parallelismList
        |> MaxParallelism
        |> partialEvalParallelism
      in
      let parallelism =
        parallelismList
        |> List.map ~f:(fun { parBlocks; parThreads } -> combinePars parBlocks parThreads)
        |> MaxParallelism
        |> partialEvalParallelism
      in
      let indexMode = Map.find loopBlockParTable label in
      let mapBody = exprToMapBody mapBody loopBlockParTable in
      let type' = List.nth_exn type' 0 in
      let lb : Corn.Expr.mapKernel =
        { label
        ; indexMode
        ; frameShape
        ; mapArgs
        ; mapIotas
        ; mapBody
        ; mapBodyMatcher
        ; mapResults
        ; type'
        }
      in
      let genMapKernel blocks threads =
        let kernel = Corn.Expr.{ kernel = lb; blocks; threads } in
        Corn.Expr.values [ Corn.Expr.MapKernel kernel; Corn.Expr.values [] ]
      in
      Corn.Expr.IfParallelismHitsCutoff
        { parallelism
        ; cutoff = IndexMode.minimumViableKernelParallelism
        ; then' = genMapKernel parBlocks parThreads
        ; else' = init
        ; type' = Corn.Expr.type' init
        }
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
      let init = rewriteWithPar lb (Map.empty (module Identifier)) in
      let consumerBodyParallelism, consumerZeroParallelism =
        collectParallelismConsumer loopBlockParTable consumer
      in
      (* let innerParallelism = *)
      (*   List.append (collectParallelism loopBlockParTable mapBody) consumerBodyParallelism *)
      (* in *)
      (* Corn.Expr.MaxParallelism *)
      (*   [ collectParallelism loopBlockParTable mapBody; consumerBodyParallelism ] *)
      let parallelismList = collectParallelism loopBlockParTable lb in
      let parallelismList = List.append parallelismList consumerBodyParallelism in
      let parallelismList =
        List.map parallelismList ~f:(fun { parBlocks; parThreads } ->
          let parBlocks = partialEvalParallelism parBlocks in
          let parThreads = partialEvalParallelism parThreads in
          { parBlocks; parThreads })
      in
      let parBlocks =
        List.map ~f:(fun p -> p.parBlocks) parallelismList
        |> MaxParallelism
        |> partialEvalParallelism
      in
      let parThreads =
        List.map ~f:(fun p -> p.parThreads) parallelismList
        |> MaxParallelism
        |> partialEvalParallelism
      in
      let parallelism =
        parallelismList
        |> List.map ~f:(fun { parBlocks; parThreads } -> combinePars parBlocks parThreads)
        |> MaxParallelism
        |> partialEvalParallelism
      in
      let consumerZeroParallelism =
        consumerZeroParallelism
        |> List.map ~f:(fun { parBlocks; parThreads } -> combinePars parBlocks parThreads)
        |> MaxParallelism
        |> partialEvalParallelism
      in
      let parallelism =
        Corn.Expr.MaxParallelism [ parallelism; consumerZeroParallelism ]
      in
      let parallelism = partialEvalParallelism parallelism in
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
      let kernel =
        Corn.Expr.LoopKernel
          Corn.Expr.{ kernel = lb; blocks = parBlocks; threads = parThreads }
      in
      Corn.Expr.IfParallelismHitsCutoff
        { parallelism
        ; cutoff = IndexMode.minimumViableKernelParallelism
        ; then' = kernel
        ; else' = init
        ; type' = Corn.Expr.type' init
        }
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
      (* let type' = [ List.nth_exn type' 0 ] in *)
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
      let op = convertScalarOp op in
      ScalarPrimitive { op; args; type' }
    | TupleDeref { index; tuple; type' = _ } ->
      let tuple = rewriteWithParHelper tuple in
      (match tuple with
       | Values { elements; type' = _ } -> List.nth_exn elements index
       | tuple -> Corn.Expr.tupleDeref ~tuple ~index)
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
    let op = convertScalarOp op in
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
     | Some subMap -> subMap)
  | rest -> MapBodyExpr (rewriteWithParDevice rest loopBlockParTable)

and exprToMapBodySubMap (expr : Nested.t) loopBlockParTable : Corn.Expr.mapBody option =
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
    let type' = List.nth_exn type' 0 in
    let mapKernel : Corn.Expr.mapKernel =
      { label
      ; frameShape
      ; indexMode
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; type'
      }
    in
    Some (MapBodySubMap (MapBodyValues [ MapBodyMap mapKernel; MapBodyValues [] ]))
  | TupleDeref { index; tuple; type' = _ } ->
    let tuple = exprToMapBodySubMap tuple loopBlockParTable in
    (match tuple with
     | None -> None
     | Some tuple ->
       (match tuple with
        | Corn.Expr.MapBodyExpr _ -> None
        | Corn.Expr.MapBodySubMap (Corn.Expr.MapBodyValues values) ->
          Some (MapBodySubMap (List.nth_exn values index))
        | Corn.Expr.MapBodySubMap subMap ->
          Some (MapBodySubMap (MapBodyDeref { tuple = subMap; index }))))
  | Values { elements; type' = _ } ->
    let elements =
      elements |> List.map ~f:(fun e -> exprToMapBodySubMap e loopBlockParTable)
    in
    let allGood =
      List.for_all elements ~f:(fun o ->
        match o with
        | Some (MapBodySubMap _) -> true
        | _ -> false)
    in
    if allGood
    then (
      let elements =
        List.map elements ~f:(fun o ->
          match o with
          | Some (MapBodySubMap subMap) -> subMap
          | _ -> raise Unreachable.default)
      in
      Some (MapBodySubMap (MapBodyValues elements)))
    else None
  | _ -> None
;;

let kernelize (expr : Nested.t) : (CompilerState.state, Corn.t, _) State.t =
  Stdio.prerr_endline "Fuse and Simplify done";
  (* This stage consists of 2 steps: collect possible paths and rewrite the program using the best one *)
  let _, paths = findAllParOptions expr IndexMode.defaultCUDA in
  (* expr *)
  (* |> [%sexp_of: Nested.t] *)
  (* |> Sexp.to_string_hum *)
  (* |> Printf.sprintf "expr in kernelize: \n%s" *)
  (* |> Stdio.prerr_endline; *)
  paths
  |> [%sexp_of: parPath list]
  |> Sexp.to_string_hum
  |> Printf.sprintf "Paths in kernelize: \n%s\n"
  |> Stdio.prerr_endline;
  match paths with
  | [] -> State.return @@ rewriteWithPar expr (Map.empty (module Identifier))
  | hd :: tl ->
    let bestPath =
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
    bestPath
    |> [%sexp_of: parPath]
    |> Sexp.to_string_hum
    |> Printf.sprintf "Best path in kernelize: \n%s\n"
    |> Stdio.prerr_endline;
    let loopBlockParTable = tableFromPath bestPath.indexModeTree in
    let newExpr = rewriteWithPar expr loopBlockParTable in
    (* let newExpr = rewriteWithPar expr (Map.empty (module Identifier)) in *)
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
