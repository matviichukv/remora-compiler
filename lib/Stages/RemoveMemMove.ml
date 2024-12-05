open! Base
open Acorn.Expr

(* Rough structure of this algorithm: *)
(* 1. Find the flow of all variables *)
(* 2. Use that information to find 'chains' and construct map to replace bindings *)
(* 3. Rewrite with map from step 2 to remove unnecessary mem copies *)
(*    note: this does not remove device->host copies, only host->device *)
(* 4. Do a second analysis + rewrite to avoid copies device to host *)
(*    if no uses of binding in a let, turn into Eseq with ComputeForSideEffects *)

(* TODO: test that order in lets is correct *)

type dfValue =
  | DFTuple of dfValue list
  | DFRef of Acorn.Mem.ref (* alias for a different thing *)
  | DFComputedValue
  | DFMem of mallocLoc
  | DFHostToDeviceCopy of dfValue
  | DFDeviceToHostCopy of dfValue
  | DFIterateOver of dfValue
  | DFDeref of
      { index : int
      ; tuple : dfValue
      }
[@@deriving sexp_of]

(* -------------------- Data Flow Map Construction -------------------------- *)
let constructDataFlowMap (expr : captures Acorn.t) =
  let rec constructDataFlowMapConsumer
    : type o i p.
      (o, i, p, captures) consumerOp
      -> (Identifier.t, dfValue, _) Map.t
      -> (Identifier.t, dfValue, _) Map.t * dfValue
    =
    fun consumer map ->
    match consumer with
    | ReducePar
        { reduce =
            { arg = { firstBinding; secondBinding; production }
            ; zero
            ; body
            ; indexMode = _
            ; d = _
            ; type' = _
            }
        ; interimResultMemDeviceInterim
        ; interimResultMemHostFinal
        ; outerBody = _
        } ->
      let productionValue = productionToDF production in
      let map = Map.update map firstBinding ~f:(fun _ -> DFIterateOver productionValue) in
      let map =
        Map.update map secondBinding ~f:(fun _ -> DFIterateOver productionValue)
      in
      let map, _ = constructDataFlowMap zero map in
      let map, _ = constructDataFlowMap body map in
      let value =
        match interimResultMemHostFinal with
        | None -> DFComputedValue
        | Some mem -> memToDF mem
      in
      let interimMemDf = memToDF interimResultMemDeviceInterim in
      let mapOpt =
        Option.map interimResultMemHostFinal ~f:(fun m -> memToDFCopy m map interimMemDf)
      in
      let map = Option.value mapOpt ~default:map in
      map, value
    | ScanPar
        { scan =
            { arg = { firstBinding; secondBinding; production }
            ; zero
            ; body
            ; indexMode = _
            ; d = _
            ; scanResultMemFinal
            ; type' = _
            }
        ; scanResultMemDeviceInterim
        } ->
      let productionValue = productionToDF production in
      let map = Map.update map firstBinding ~f:(fun _ -> DFIterateOver productionValue) in
      let map =
        Map.update map secondBinding ~f:(fun _ -> DFIterateOver productionValue)
      in
      let map, _ = constructDataFlowMap zero map in
      let map, _ = constructDataFlowMap body map in
      let rec matcher memHost memDevice derefStack =
        match memHost, memDevice with
        | Acorn.Mem.Ref refHost, Acorn.Mem.Ref refDev ->
          [ refHost.id, DFDeviceToHostCopy (DFRef refDev) ]
        | ( Acorn.Mem.Index { mem = memHost; offset = _; type' = _ }
          , Acorn.Mem.Index { mem = memDev; offset = _; type' = _ } ) ->
          matcher memHost memDev derefStack
        | ( Acorn.Mem.TupleDeref { tuple = tupleHost; index = indexHost; type' = _ }
          , Acorn.Mem.TupleDeref { tuple = tupleDev; index = indexDev; type' = _ } ) ->
          matcher tupleHost tupleDev ((indexHost, indexDev) :: derefStack)
        | ( Acorn.Mem.Values { elements = elementsHost; type' = _ }
          , Acorn.Mem.Values { elements = elementsDev; type' = _ } ) ->
          (match derefStack with
           | [] ->
             List.zip_exn elementsHost elementsDev
             |> List.map ~f:(fun (h, d) -> matcher h d derefStack)
             |> List.concat
           | (hostIdx, devIdx) :: rest ->
             matcher
               (List.nth_exn elementsHost hostIdx)
               (List.nth_exn elementsDev devIdx)
               rest)
        | _ -> raise Unreachable.default
      in
      let entries = matcher scanResultMemFinal scanResultMemDeviceInterim [] in
      let map =
        List.fold entries ~init:map ~f:(fun acc (id, value) ->
          Map.update acc id ~f:(fun _ -> value))
      in
      map, memToDF scanResultMemFinal
    | ReduceSeq
        { arg = { firstBinding; secondBinding; production }
        ; zero
        ; body
        ; indexMode = _
        ; d = _
        ; type' = _
        } ->
      let productionValue = productionToDF production in
      let map = Map.update map firstBinding ~f:(fun _ -> DFIterateOver productionValue) in
      let map =
        Map.update map secondBinding ~f:(fun _ -> DFIterateOver productionValue)
      in
      let map, _ = constructDataFlowMap zero map in
      let map, value = constructDataFlowMap body map in
      map, value
    | ScanSeq
        { arg = { firstBinding; secondBinding; production }
        ; zero
        ; body
        ; indexMode = _
        ; d = _
        ; scanResultMemFinal
        ; type' = _
        } ->
      let productionValue = productionToDF production in
      let map = Map.update map firstBinding ~f:(fun _ -> DFIterateOver productionValue) in
      let map =
        Map.update map secondBinding ~f:(fun _ -> DFIterateOver productionValue)
      in
      let map, _ = constructDataFlowMap zero map in
      let map, _ = constructDataFlowMap body map in
      map, memToDF scanResultMemFinal
    | Scatter _ -> map, DFComputedValue
    | Fold
        { zeroArg = { zeroBinding; zeroValue }
        ; arrayArgs
        ; mappedMemArgs
        ; reverse = _
        ; body
        ; d = _
        ; character
        ; type' = _
        } ->
      let map, zeroValue = constructDataFlowMap zeroValue map in
      let map = Map.update map zeroBinding ~f:(fun _ -> zeroValue) in
      let map =
        List.fold arrayArgs ~init:map ~f:(fun map { binding; production } ->
          Map.update map binding ~f:(fun _ ->
            productionToDF (ProductionTupleAtom production)))
      in
      let map =
        List.fold mappedMemArgs ~init:map ~f:(fun map { memBinding; mem } ->
          Map.update map memBinding ~f:(fun _ -> memToDF mem))
      in
      let map, _ = constructDataFlowMap body map in
      let value =
        match character with
        | Fold -> DFComputedValue
        | Trace mem -> memToDF mem
      in
      map, value
  and constructDataFlowMapLoopBlock
    : type o i p e.
      (o, i, p, _, e) loopBlock
      -> (Identifier.t, dfValue, _) Map.t
      -> (Identifier.t, dfValue, _) Map.t * dfValue
    =
    fun loopBlock map ->
    match loopBlock with
    | { frameShape = _
      ; indexMode = _
      ; mapArgs
      ; mapMemArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher = _
      ; mapResults = _
      ; mapResultMemFinal
      ; consumer
      ; type' = _
      } ->
      let argsDF =
        List.map mapArgs ~f:(fun { binding; ref = { id; type' } } ->
          binding, DFIterateOver (DFRef { id; type' }))
      in
      let memArgsDF =
        List.map mapMemArgs ~f:(fun { memBinding; mem } ->
          memBinding, DFIterateOver (memToDF mem))
      in
      let iotaArgsDF = List.map mapIotas ~f:(fun id -> id, DFComputedValue) in
      let map =
        List.fold
          (argsDF @ memArgsDF @ iotaArgsDF)
          ~init:map
          ~f:(fun map (id, df) -> Map.update map id ~f:(fun _ -> df))
      in
      let map, _ = constructDataFlowMap mapBody map in
      let value = flattenDFTuple (memToDF mapResultMemFinal) in
      let consumerResOpt =
        Maybe.map consumer ~f:(fun c -> constructDataFlowMapConsumer c map)
      in
      let consumerMap, consumerValue =
        match consumerResOpt with
        | Just res -> res
        | Nothing -> map, value
      in
      consumerMap, DFTuple [ value; consumerValue ]
  and constructDataFlowMap
    : type i p e. (i, captures) t -> (_, _, _) Map.t -> (_, _, _) Map.t * dfValue
    =
    fun expr map ->
    match expr with
    | Ref { id; type' } -> map, DFRef { id; type' }
    | BoxValue { box; type' = _ } -> constructDataFlowMap box map
    | IndexLet { indexArgs = _; body; type' = _ } ->
      (* let map = List.fold indexArgs ~init:map ~f:(fun _ -> _) in *)
      constructDataFlowMap body map
    | MallocLet { memArgs; body } ->
      let newMap =
        List.fold memArgs ~init:map ~f:(fun acc { memBinding; memType = _; memLoc } ->
          Map.update acc memBinding ~f:(fun _ -> DFMem memLoc))
      in
      constructDataFlowMap body newMap
    | ReifyDimensionIndex { dim = _ } -> map, DFComputedValue
    | ShapeProd _ -> map, DFComputedValue
    | LoopBlock loopBlock -> constructDataFlowMapLoopBlock loopBlock map
    | LoopKernel
        { kernel = { mapResultMemDeviceInterim; loopBlock }
        ; captures = { exprCaptures; indexCaptures = _; memCaptures }
        ; blocks = _
        ; threads = _
        } ->
      let captureMap =
        List.fold
          (Map.to_alist exprCaptures @ Map.to_alist memCaptures)
          ~init:map
          ~f:(fun map (id, type') ->
            Map.update map id ~f:(function
              | None -> DFHostToDeviceCopy (DFRef { id; type' })
              | Some value -> DFHostToDeviceCopy value))
      in
      let interimMemDf = memToDF mapResultMemDeviceInterim in
      let captureMap = memToDFCopy loopBlock.mapResultMemFinal captureMap interimMemDf in
      let loopBlockMap, loopBlockValue =
        constructDataFlowMapLoopBlock loopBlock captureMap
      in
      loopBlockMap, loopBlockValue
      | StaticAllocLet { args; body }
      | Let { args; body } ->
      let newMap =
        List.fold args ~init:map ~f:(fun acc { binding; value } ->
          let acc, value = constructDataFlowMap value acc in
          Map.update acc binding ~f:(fun _ -> value))
      in
      let bodyMap, body = constructDataFlowMap body newMap in
      bodyMap, body
      (* While indices contain technically speaking arbitrary expressions, *)
      (* none of the expression that *will* end up there are interesting *)
    | Box { indices = _; body; type' = _ } -> constructDataFlowMap body map
    | StaticArrayInit _ -> map, DFComputedValue
    | Literal _ -> map, DFComputedValue
    | Values { elements; type' = _ } ->
      let values, map =
        List.fold_right elements ~init:([], map) ~f:(fun e (vals, map) ->
          let map, value = constructDataFlowMap e map in
          value :: vals, map)
      in
      map, DFTuple values
    | ScalarPrimitive { op = _; args; type' = _ } ->
      let value = DFComputedValue in
      let map =
        List.fold args ~init:map ~f:(fun acc a ->
          let map, _ = constructDataFlowMap a acc in
          map)
      in
      map, value
    | TupleDeref { index; tuple; type' = _ } ->
      let newMap, value = constructDataFlowMap tuple map in
      (match value with
       | DFTuple elements -> newMap, List.nth_exn elements index
       | other -> newMap, DFDeref { index; tuple = other })
    | ContiguousSubArray _ -> map, DFComputedValue
    | IfParallelismHitsCutoff _ -> raise Unimplemented.default
    | Eseq { statement; expr; type' = _ } ->
      let statementMap = constructDataFlowMapStatement statement map in
      constructDataFlowMap expr statementMap
    | Getmem { addr; type' = _ } ->
      let value = memToDF addr in
      map, value
  and constructDataFlowMapMapInKernel (mapInKernel : _ mapInKernel) map =
    match mapInKernel with
    | { frameShape = _
      ; indexMode = _
      ; mapArgs
      ; mapMemArgs
      ; mapIotas = _
      ; mapBody
      ; type' = _
      } ->
      let map =
        List.fold mapArgs ~init:map ~f:(fun map { binding; ref = { id; type' } } ->
          Map.update map binding ~f:(fun _ -> DFIterateOver (DFRef { id; type' })))
      in
      let map =
        List.fold mapMemArgs ~init:map ~f:(fun map { memBinding; mem } ->
          Map.update map memBinding ~f:(fun _ -> DFIterateOver (memToDF mem)))
      in
      (match mapBody with
       | MapBodyStatement statement -> constructDataFlowMapStatement statement map
       | MapBodySubMaps subMapList ->
         List.fold subMapList ~init:map ~f:(fun map submap ->
           constructDataFlowMapMapInKernel submap map))
  and constructDataFlowMapStatement
    : type i. (i, captures) statement -> (_, _, _) Map.t -> (_, _, _) Map.t
    =
    fun statement map ->
    match statement with
    | Putmem _ -> map
    | MapKernel
        { kernel =
            { label = _
            ; map = kernelMap
            ; mapResultMemDeviceInterim
            ; mapResultMemHostFinal
            }
        ; captures = { exprCaptures; indexCaptures = _; memCaptures }
        ; blocks = _
        ; threads = _
        } ->
      let map =
        List.fold
          (Map.to_alist exprCaptures @ Map.to_alist memCaptures)
          ~init:map
          ~f:(fun map (id, type') ->
            Map.update map id ~f:(function
              | None -> DFHostToDeviceCopy (DFRef { id; type' })
              | Some value -> DFHostToDeviceCopy value))
      in
      let map = constructDataFlowMapMapInKernel kernelMap map in
      let interimMemDf = memToDF mapResultMemDeviceInterim in
      let map = memToDFCopy mapResultMemHostFinal map interimMemDf in
      map
    | ComputeForSideEffects expr ->
      let map, _ = constructDataFlowMap expr map in
      map
    | Statements statements ->
      List.fold statements ~init:map ~f:(fun acc s -> constructDataFlowMapStatement s acc)
    | SLet { args; body } ->
      let map =
        List.fold args ~init:map ~f:(fun acc { binding; value } ->
          let map, value = constructDataFlowMap value acc in
          Map.update map binding ~f:(fun _ -> value))
      in
      constructDataFlowMapStatement body map
    | SMallocLet { memArgs; body } ->
      let map =
        List.fold memArgs ~init:map ~f:(fun map { memBinding; memType = _; memLoc } ->
          Map.update map memBinding ~f:(fun _ -> DFMem memLoc))
      in
      constructDataFlowMapStatement body map
    | ReifyShapeIndex _ -> map
  and memToDF addr =
    match addr with
    | Acorn.Mem.Ref ref -> DFRef ref
    | Acorn.Mem.TupleDeref { tuple; index; type' = _ } ->
      let tuple = memToDF tuple in
      DFDeref { index; tuple }
    | Acorn.Mem.Values { elements; type' = _ } -> DFTuple (List.map elements ~f:memToDF)
    | Acorn.Mem.Index { mem; offset = _; type' = _ } -> memToDF mem
  and memToDFCopy (mem : Acorn.Mem.t) map ?(f = fun e -> e) (targetMemDf : dfValue) =
    match mem with
    | Acorn.Mem.Ref { id; type' = _ } ->
      Map.update map id ~f:(function _ -> DFDeviceToHostCopy (f targetMemDf))
    | Acorn.Mem.Values { elements; type' = _ } ->
      List.foldi elements ~init:map ~f:(fun index map e ->
        memToDFCopy e map ?f:(Some (fun tuple -> DFDeref { tuple; index })) targetMemDf)
    | Acorn.Mem.Index { mem; offset = _; type' = _ } ->
      memToDFCopy ?f:(Some f) mem map targetMemDf
    | Acorn.Mem.TupleDeref { tuple; index; type' = _ } ->
      memToDFCopy
        tuple
        map
        targetMemDf
        ?f:
          (Some
             (fun df ->
               DFTuple (List.append (List.init index ~f:(fun _ -> DFTuple [])) [ df ])))
  and productionToDF prod =
    match prod with
    | ProductionTuple { elements; type' = _ } ->
      DFTuple (List.map elements ~f:productionToDF)
    | ProductionTupleAtom { productionId = id; type' } -> DFRef { id; type' }
  and flattenDFTuple dfValue =
    match dfValue with
    | DFTuple elements -> DFTuple (List.concat_map elements ~f:dfValueToFlatList)
    | DFRef r -> DFRef r
    | DFComputedValue -> DFComputedValue
    | DFMem mem -> DFMem mem
    | DFHostToDeviceCopy id -> DFHostToDeviceCopy id
    | DFDeviceToHostCopy id -> DFDeviceToHostCopy id
    | DFIterateOver value -> DFIterateOver value
    | DFDeref value -> DFDeref value
  and dfValueToFlatList dfValue =
    match dfValue with
    | DFTuple elements -> List.concat_map elements ~f:dfValueToFlatList
    | DFRef id -> [ DFRef id ]
    | DFComputedValue -> [ DFComputedValue ]
    | DFMem mem -> [ DFMem mem ]
    | DFHostToDeviceCopy id -> [ DFHostToDeviceCopy id ]
    | DFDeviceToHostCopy id -> [ DFDeviceToHostCopy id ]
    | DFIterateOver dfValue -> [ DFIterateOver dfValue ]
    | DFDeref deref -> [ DFDeref deref ]
  in
  constructDataFlowMap expr (Map.empty (module Identifier))
;;

(* -------------------- Replacement Map Construction -------------------------- *)

type chainFollowRes =
  | NothingFound
  | Done of Acorn.Mem.t
  | NotDone of
      { id : Identifier.t
      ; derefStack : int list
      ; traversedDeviceToHost : bool
      ; traversedHostToDevice : bool
      }

(* Construct a map from original to 'replacement' binding *)
let rec constructReplaceMap
  : type l.
    (l, captures) t
    -> (Identifier.t, dfValue, _) Map.t
    -> (Identifier.t, Acorn.Mem.t, _) Map.t
  =
  fun expr dfMap ->
  let emptyMap = Map.empty (module Identifier) in
  match expr with
  | Ref _ -> emptyMap
  | BoxValue { box; type' = _ } -> constructReplaceMap box dfMap
  | IndexLet { indexArgs; body; type' = _ } ->
    let argMaps =
      List.map indexArgs ~f:(function { indexBinding = _; indexValue; sort = _ } ->
        (match indexValue with
         | Runtime r -> constructReplaceMap r dfMap
         | FromBox { box; i = _ } -> constructReplaceMap box dfMap))
    in
    let bodyMap = constructReplaceMap body dfMap in
    List.fold argMaps ~init:bodyMap ~f:(Map.merge_skewed ~combine:(fun ~key:_ v _ -> v))
  | MallocLet { memArgs = _; body } -> constructReplaceMap body dfMap
  | ReifyDimensionIndex _ -> emptyMap
  | ShapeProd _ -> emptyMap
  | LoopBlock
      { frameShape = _
      ; indexMode = _
      ; mapArgs = _
      ; mapMemArgs = _
      ; mapIotas = _
      ; mapBody
      ; mapBodyMatcher = _
      ; mapResults = _
      ; mapResultMemFinal = _
      ; consumer
      ; type' = _
      } ->
    (* We don't do anything with args here because this isn't a device-host boundary *)
    let bodyMap = constructReplaceMap mapBody dfMap in
    let consumerMapOpt =
      Maybe.map consumer ~f:(fun c -> constructReplaceMapConsumer c dfMap)
    in
    let consumerMap =
      match consumerMapOpt with
      | Nothing -> emptyMap
      | Just map -> map
    in
    Map.merge_skewed bodyMap consumerMap ~combine:(fun ~key:_ v _ -> v)
  | LoopKernel kernel -> constructReplaceMapLoopblockKernel kernel dfMap
  | StaticAllocLet { args; body }
  | Let { args; body } ->
    let argMaps =
      List.map args ~f:(fun { binding = _; value } -> constructReplaceMap value dfMap)
    in
    let bodyMap = constructReplaceMap body dfMap in
    List.fold argMaps ~init:bodyMap ~f:(Map.merge_skewed ~combine:(fun ~key:_ v _ -> v))
  | Box { indices = _; body; type' = _ } -> constructReplaceMap body dfMap
  | StaticArrayInit _ -> emptyMap
  | Literal _ -> emptyMap
  | Values { elements; type' = _ } ->
    let elementMaps = List.map elements ~f:(fun e -> constructReplaceMap e dfMap) in
    List.fold
      elementMaps
      ~init:emptyMap
      ~f:(Map.merge_skewed ~combine:(fun ~key:_ v _ -> v))
  | ScalarPrimitive { op = _; args; type' = _ } ->
    let argMaps = List.map args ~f:(fun a -> constructReplaceMap a dfMap) in
    List.fold argMaps ~init:emptyMap ~f:(Map.merge_skewed ~combine:(fun ~key:_ v _ -> v))
  | TupleDeref { index = _; tuple; type' = _ } -> constructReplaceMap tuple dfMap
  | ContiguousSubArray
      { arrayArg; indexArg; originalShape = _; resultShape = _; type' = _ } ->
    let arrayMap = constructReplaceMap arrayArg dfMap in
    let indexMap = constructReplaceMap indexArg dfMap in
    Map.merge_skewed arrayMap indexMap ~combine:(fun ~key:_ v _ -> v)
  | IfParallelismHitsCutoff { parallelism = _; cutoff = _; then'; else'; type' = _ } ->
    let thenMap = constructReplaceMap then' dfMap in
    let elseMap = constructReplaceMap else' dfMap in
    Map.merge_skewed thenMap elseMap ~combine:(fun ~key:_ v _ -> v)
  | Eseq { statement; expr; type' = _ } ->
    let statementMap = constructReplaceMapStatement statement dfMap in
    let exprMap = constructReplaceMap expr dfMap in
    Map.merge_skewed statementMap exprMap ~combine:(fun ~key:_ v _ -> v)
  | Getmem _ -> emptyMap

and constructReplaceMapStatement
  : type l. l statementWithCaptures -> (_, _, _) Map.t -> (_, _, _) Map.t
  =
  fun statement dfMap ->
  match statement with
  | MapKernel
      { kernel
      ; captures = { exprCaptures; indexCaptures = _; memCaptures = _ }
      ; blocks = _
      ; threads = _
      } ->
    let captureMap =
      Map.to_alist exprCaptures
      |> List.filter_map ~f:(fun (id, _) ->
        Stdio.prerr_endline (Printf.sprintf "Looking at capture %s" (Identifier.show id));
        match followChain id dfMap with
        | Some mem -> Some (id, mem)
        | None -> None)
      |> Map.of_alist_exn (module Identifier)
    in
    let kernelMap = constructReplaceMapMapKernel kernel dfMap in
    Map.merge_skewed captureMap kernelMap ~combine:(fun ~key:_ v _ -> v)
  | Putmem { expr; addr = _; type' = _ } -> constructReplaceMap expr dfMap
  | ComputeForSideEffects expr -> constructReplaceMap expr dfMap
  | Statements statements ->
    let maps = List.map statements ~f:(fun s -> constructReplaceMapStatement s dfMap) in
    List.fold
      maps
      ~init:(Map.empty (module Identifier))
      ~f:(Map.merge_skewed ~combine:(fun ~key:_ v _ -> v))
  | SLet { args; body } ->
    let argMaps =
      List.map args ~f:(fun { binding = _; value } -> constructReplaceMap value dfMap)
    in
    let bodyMap = constructReplaceMapStatement body dfMap in
    List.fold argMaps ~init:bodyMap ~f:(Map.merge_skewed ~combine:(fun ~key:_ v _ -> v))
  | SMallocLet { memArgs = _; body } -> constructReplaceMapStatement body dfMap
  | ReifyShapeIndex _ -> Map.empty (module Identifier)

and constructReplaceMapConsumer
  : type o i p. (o, i, p, captures) consumerOp -> (_, _, _) Map.t -> (_, _, _) Map.t
  =
  fun consumer dfMap ->
  let rec constructReplacePairsProduction (tuple : productionTuple) =
    match tuple with
    | ProductionTuple { elements; type' = _ } ->
      elements |> List.map ~f:constructReplacePairsProduction |> List.concat
    | ProductionTupleAtom { productionId; type' = _ } ->
      (match followChain productionId dfMap with
       | Some mem -> [ productionId, mem ]
       | None -> [])
  in
  match consumer with
  | ReduceSeq { arg = _; zero; body; indexMode = _; d = _; type' = _ } ->
    let bodyMap = constructReplaceMap body dfMap in
    let zeroMap = constructReplaceMap zero dfMap in
    Map.merge_skewed bodyMap zeroMap ~combine:(fun ~key:_ v _ -> v)
  | ReducePar
      { reduce = { arg; zero; body; indexMode = _; d = _; type' = _ }
      ; interimResultMemDeviceInterim = _
      ; interimResultMemHostFinal = _
      ; outerBody = _
      } ->
    let zeroMap = constructReplaceMap zero dfMap in
    let bodyMap = constructReplaceMap body dfMap in
    let argMap =
      constructReplacePairsProduction arg.production
      |> Map.of_alist_exn (module Identifier)
    in
    let map = Map.merge_skewed zeroMap bodyMap ~combine:(fun ~key:_ v _ -> v) in
    Map.merge_skewed argMap map ~combine:(fun ~key:_ v _ -> v)
  | ScanSeq
      { arg = _; zero; body; indexMode = _; d = _; scanResultMemFinal = _; type' = _ } ->
    let bodyMap = constructReplaceMap body dfMap in
    let zeroMap = constructReplaceMap zero dfMap in
    Map.merge_skewed bodyMap zeroMap ~combine:(fun ~key:_ v _ -> v)
  | ScanPar
      { scan =
          { arg; zero; body; indexMode = _; d = _; scanResultMemFinal = _; type' = _ }
      ; scanResultMemDeviceInterim = _
      } ->
    let zeroMap = constructReplaceMap zero dfMap in
    let bodyMap = constructReplaceMap body dfMap in
    let argMap =
      constructReplacePairsProduction arg.production
      |> Map.of_alist_exn (module Identifier)
    in
    let map = Map.merge_skewed zeroMap bodyMap ~combine:(fun ~key:_ v _ -> v) in
    Map.merge_skewed argMap map ~combine:(fun ~key:_ v _ -> v)
  | Scatter
      { valuesArg
      ; indicesArg
      ; dIn = _
      ; dOut = _
      ; memInterim = _
      ; memFinal = _
      ; type' = _
      } ->
    let valueReplacementOpt = followChain valuesArg.productionId dfMap in
    let indicesReplacementOpt = followChain indicesArg.productionId dfMap in
    let map =
      match valueReplacementOpt with
      | None -> Map.empty (module Identifier)
      | Some mem -> Map.of_alist_exn (module Identifier) [ valuesArg.productionId, mem ]
    in
    let map =
      match indicesReplacementOpt with
      | None -> map
      | Some mem -> Map.update map indicesArg.productionId ~f:(fun _ -> mem)
    in
    map
  | Fold
      { zeroArg = { zeroBinding = _; zeroValue }
      ; arrayArgs = _
      ; mappedMemArgs = _
      ; reverse = _
      ; body
      ; d = _
      ; character = _
      ; type' = _
      } ->
    (* No processing of arrayArgs since those are productions and there is no boundary here *)
    let zeroMap = constructReplaceMap zeroValue dfMap in
    let bodyMap = constructReplaceMap body dfMap in
    Map.merge_skewed zeroMap bodyMap ~combine:(fun ~key:_ v _ -> v)

and constructReplaceMapLoopblockKernel
  : type i o e.
    ((i, o, captures, e) parLoopBlock, captures) kernel
    -> (_, _, _) Map.t
    -> (_, _, _) Map.t
  =
  fun loopblock dfMap ->
  match loopblock with
  | { kernel =
        { mapResultMemDeviceInterim = _
        ; loopBlock =
            { frameShape = _
            ; indexMode = _
            ; mapArgs = _
            ; mapMemArgs = _
            ; mapIotas = _
            ; mapBody
            ; mapBodyMatcher = _
            ; mapResults = _
            ; mapResultMemFinal = _
            ; consumer
            ; type' = _
            }
        }
    ; captures = { exprCaptures; memCaptures = _; indexCaptures = _ }
    ; blocks = _
    ; threads = _
    } ->
    let bodyMap = constructReplaceMap mapBody dfMap in
    let captureMap =
      Map.to_alist exprCaptures
      |> List.filter_map ~f:(fun (id, _) ->
        Stdio.prerr_endline (Printf.sprintf "Looking at capture %s" (Identifier.show id));
        match followChain id dfMap with
        | Some mem -> Some (id, mem)
        | None -> None)
      |> Map.of_alist_exn (module Identifier)
    in
    let consumerMapOpt =
      Maybe.map consumer ~f:(fun c -> constructReplaceMapConsumer c dfMap)
    in
    let consumerMap =
      match consumerMapOpt with
      | Just map -> map
      | Nothing -> Map.empty (module Identifier)
    in
    let map = Map.merge_skewed bodyMap captureMap ~combine:(fun ~key:_ v _ -> v) in
    Map.merge_skewed map consumerMap ~combine:(fun ~key:_ v _ -> v)

and constructReplaceMapMapKernel
  : captures mapKernel -> (_, _, _) Map.t -> (_, _, _) Map.t
  =
  fun mapKernel dfMap ->
  match mapKernel with
  | { label = _; map; mapResultMemDeviceInterim = _; mapResultMemHostFinal = _ } ->
    constructReplaceMapMapInKernel map dfMap

and constructReplaceMapMapInKernel
  : captures mapInKernel -> (_, _, _) Map.t -> (_, _, _) Map.t
  =
  fun mapInKernel dfMap ->
  match mapInKernel with
  | { frameShape = _
    ; indexMode = _
    ; mapArgs = _
    ; mapMemArgs = _
    ; mapIotas = _
    ; mapBody
    ; type' = _
    } -> constructReplaceMapMapBody mapBody dfMap

and constructReplaceMapMapBody : captures mapBody -> (_, _, _) Map.t -> (_, _, _) Map.t =
  fun mapBody dfMap ->
  match mapBody with
  | MapBodyStatement statement -> constructReplaceMapStatement statement dfMap
  | MapBodySubMaps subMaps ->
    let maps = List.map subMaps ~f:(fun m -> constructReplaceMapMapInKernel m dfMap) in
    List.fold
      maps
      ~init:(Map.empty (module Identifier))
      ~f:(Map.merge_skewed ~combine:(fun ~key:_ v _ -> v))

and followChain id dfMap : Acorn.Mem.t option =
  (* traverse a single row from the dfMap *)
  let rec traverseDFEntry
    (df : dfValue)
    ~derefStack
    ~traversedHostToDevice
    ~traversedDeviceToHost
    =
    match df with
    | DFTuple dfValues ->
      (match derefStack with
       | hd :: tl ->
         (match List.nth dfValues hd with
          | None -> NothingFound
          | Some df ->
            traverseDFEntry
              df
              ~derefStack:tl
              ~traversedHostToDevice
              ~traversedDeviceToHost)
       | [] ->
         (* Simplified version, all elements have to terminate this entry otherwise we stop *)
         let elementsResult =
           List.map dfValues ~f:(fun df ->
             traverseDFEntry df ~traversedHostToDevice ~traversedDeviceToHost ~derefStack)
         in
         if List.for_all elementsResult ~f:(function
              | NothingFound -> false
              | NotDone _ -> false
              | Done _ -> true)
         then
           Done
             (Acorn.Mem.values
                (List.filter_map elementsResult ~f:(function
                  | NothingFound -> None
                  | NotDone _ -> None
                  | Done mem -> Some mem)))
         else NothingFound)
    | DFRef ref ->
      if traversedHostToDevice && traversedDeviceToHost
      then (
        let mem = Acorn.Mem.Ref ref in
        let mem =
          List.fold_left derefStack ~init:mem ~f:(fun acc deref ->
            Acorn.Mem.tupleDeref ~tuple:acc ~index:deref)
        in
        Done mem)
      else
        NotDone { id = ref.id; derefStack; traversedHostToDevice; traversedDeviceToHost }
    | DFComputedValue -> NothingFound
    | DFMem _ -> NothingFound
    | DFHostToDeviceCopy df ->
      traverseDFEntry df ~derefStack ~traversedHostToDevice:true ~traversedDeviceToHost
    | DFDeviceToHostCopy df ->
      traverseDFEntry df ~derefStack ~traversedHostToDevice ~traversedDeviceToHost:true
    | DFIterateOver _ ->
      NothingFound
      (* traverseDFEntry df ~derefStack ~traversedHostToDevice ~traversedDeviceToHost *)
    | DFDeref { index; tuple } ->
      traverseDFEntry
        tuple
        ~derefStack:(index :: derefStack)
        ~traversedHostToDevice
        ~traversedDeviceToHost
  and followChainRec id dfMap ~derefStack ~traversedDeviceToHost ~traversedHostToDevice =
    match Map.find dfMap id with
    | None -> None
    | Some df ->
      let res =
        traverseDFEntry df ~derefStack ~traversedHostToDevice ~traversedDeviceToHost
      in
      (match res with
       | NothingFound -> None
       | Done mem -> Some (mem, true, true) (* | NotDone _ -> None) *)
       | NotDone { id; derefStack; traversedDeviceToHost; traversedHostToDevice } ->
         followChainRec id dfMap ~derefStack ~traversedDeviceToHost ~traversedHostToDevice)
    (* (match restChainRes with *)
    (*  | None -> *)
    (*    let mem = memCont (Acorn.Mem.Ref _) in *)
    (*    Some (mem, traversedDeviceToHost, traversedHostToDevice) *)
    (*  | Some (memRest, traversedDeviceToHostRest, traversedHostToDeviceRest) -> *)
    (*    let mem = memCont memRest in *)
    (*    Some *)
    (*      ( mem *)
    (*      , traversedDeviceToHost && traversedDeviceToHostRest *)
    (*      , traversedHostToDevice && traversedHostToDeviceRest ))) *)
  in
  Stdio.prerr_endline (Printf.sprintf "Following chain on %s" (Identifier.show id));
  let chainResult =
    followChainRec
      id
      dfMap
      ~derefStack:[]
      ~traversedDeviceToHost:false
      ~traversedHostToDevice:false
  in
  match chainResult with
  | Some (mem, true, true) -> Some mem
  | _ -> None
;;

(* and followChain id dfMap type' = *)
(*   let rec traverseDF (df : dfValue) dfMap derefStack ~traversedDH ~traversedHD = *)
(*     match df with *)
(*     | DFTuple elements -> *)
(*       (match derefStack with *)
(*        | [] -> None *)
(*        | hd :: tl -> *)
(*          let element = List.nth_exn elements hd in *)
(*          traverseDF element dfMap tl ~traversedDH ~traversedHD) *)
(*     | DFRef id -> *)
(*       let mem = Acorn.Mem.Ref { id; type' } in *)
(*       (match derefStack with *)
(*        | [] -> Some (id, mem, traversedDH, traversedHD) *)
(*        | derefs -> *)
(*          let mem = *)
(*            List.fold_left derefs ~init:mem ~f:(fun acc d -> *)
(*              Acorn.Mem.tupleDeref ~tuple:acc ~index:d) *)
(*          in *)
(*          Some (id, mem, traversedDH, traversedHD)) *)
(*     | DFComputedValue -> None *)
(*     | DFMem _ -> None *)
(*     | DFHostToDeviceCopy df -> *)
(*       traverseDF df dfMap derefStack ~traversedDH ~traversedHD:true *)
(*     | DFDeviceToHostCopy df -> *)
(*       traverseDF df dfMap derefStack ~traversedDH:true ~traversedHD *)
(*     | DFIterateOver df -> traverseDF df dfMap derefStack ~traversedDH ~traversedHD *)
(*     | DFDeref { index; tuple } -> *)
(*       traverseDF tuple dfMap (index :: derefStack) ~traversedDH ~traversedHD *)
(*   in *)
(*   let followRec traverseRes = *)
(*     match traverseRes with *)
(*     | None -> None *)
(*     | Some (id, mem, true, true) -> Some (id, true, true) *)
(*     | Some (id, mem, traversedDH, traversedHD) -> *)
(*       let restRes = followChain id dfMap type' in *)
(*       (match restRes with *)
(*        | None -> traverseRes *)
(*        | Some (idRest, memRest, traversedDHRest, traversedHDRest) -> *)
(*          if (traversedDH || traversedDHRest) && (traversedHD || traversedHDRest) *)
(*          then ( *)
(*            Stdio.prerr_endline "Got a full chain"; *)
(*            Some (idRest, true, true)) *)
(*          else if traversedDHRest || traversedDH || traversedHD || traversedHDRest *)
(*          then Some (idRest, traversedDH || traversedDHRest, traversedHD || traversedHDRest) *)
(*          else None) *)
(*   in *)
(*   match Map.find dfMap id with *)
(*   | Some df -> *)
(*     (match df with *)
(*      | DFTuple _ as tuple -> *)
(*        let resOpt = traverseDF tuple dfMap [] ~traversedDH:false ~traversedHD:false in *)
(*        followRec resOpt *)
(*      | DFRef id -> *)
(*        let mem = Acorn.Mem.Ref { id; type' = _ } in *)
(*        followRec (Some (mem, false, false)) *)
(*      | DFMem _ -> None *)
(*      | DFHostToDeviceCopy df -> *)
(*        let resOpt = traverseDF df dfMap [] ~traversedHD:true ~traversedDH:false in *)
(*        Stdio.prerr_endline (Sexp.to_string_hum ([%sexp_of: Identifier.t] id)); *)
(*        Stdio.prerr_endline *)
(*          (Sexp.to_string_hum ([%sexp_of: (Identifier.t * Acorn.Mem.t * bool * bool) option] resOpt)); *)
(*        followRec resOpt *)
(*      | DFDeviceToHostCopy df -> *)
(*        let resOpt = traverseDF df dfMap [] ~traversedDH:true ~traversedHD:false in *)
(*        followRec resOpt *)
(*      | DFDeref { index; tuple } -> *)
(*        let resOpt = *)
(*          traverseDF tuple dfMap [ index ] ~traversedDH:false ~traversedHD:false *)
(*        in *)
(*        followRec resOpt *)
(*      | DFIterateOver df -> *)
(*        let resOpt = traverseDF df dfMap [] ~traversedDH:false ~traversedHD:false in *)
(*        followRec resOpt *)
(*      | DFComputedValue -> None) *)
(*   (\* match on df, and follow the chain, stop on stuff like compute *\) *)
(*   | None -> None *)

(* -------------------- Rewrite #1 (Elim host->dev) ---------------------- *)
(* Arguments are: *)
(* expr - expression to rewrite *)
(* replaceMap - map from expr ids to mem ids to replace in captures and loop args *)
(* exprToMemRefs - list of bindings that should be used as mem instead of expr *)
(*                 do not populate when calling this will be done inside the function *)
let rec removeHostToDevCopy
  : type l.
    (l, captures) t
    -> (Identifier.t, Acorn.Mem.t, _) Map.t
    -> Identifier.t list
    -> (l, captures) t
  =
  fun expr replaceMap exprToMemRefs ->
  match expr with
  | Ref { id; type' } ->
    (match List.mem exprToMemRefs id ~equal:Identifier.equal with
     | true -> Getmem { addr = Acorn.Mem.Ref { id; type' }; type' }
     | false ->
       (match Map.find replaceMap id with
        | Some addr -> Getmem { addr; type' }
        | None -> Ref { id; type' }))
  | BoxValue { box; type' } ->
    let box = removeHostToDevCopy box replaceMap exprToMemRefs in
    BoxValue { box; type' }
  | IndexLet { indexArgs; body; type' } ->
    let indexArgs =
      List.map indexArgs ~f:(fun { indexBinding; indexValue; sort } ->
        let indexValue =
          match indexValue with
          | Runtime v -> Runtime (removeHostToDevCopy v replaceMap exprToMemRefs)
          | FromBox { box; i } ->
            let box = removeHostToDevCopy box replaceMap exprToMemRefs in
            FromBox { box; i }
        in
        { indexBinding; indexValue; sort })
    in
    let body = removeHostToDevCopy body replaceMap exprToMemRefs in
    IndexLet { indexArgs; body; type' }
  | MallocLet { memArgs; body } ->
    let body = removeHostToDevCopy body replaceMap exprToMemRefs in
    MallocLet { memArgs; body }
  | ReifyDimensionIndex i -> ReifyDimensionIndex i
  | ShapeProd s -> ShapeProd s
  | LoopBlock lb ->
    let lb = removeHostToDevCopyLoopBlock lb replaceMap exprToMemRefs in
    LoopBlock lb
  | LoopKernel { kernel; captures; blocks; threads } ->
    let kernel = removeHostToDevCopyKernel kernel replaceMap exprToMemRefs in
    let captures = removeHostToDevCopyCaptures captures replaceMap exprToMemRefs in
    LoopKernel { kernel; captures; blocks; threads }
  | StaticAllocLet { args; body } ->
    let args =
      List.map args ~f:(fun { binding; value } ->
        { binding; value = removeHostToDevCopy value replaceMap exprToMemRefs })
    in
    let body = removeHostToDevCopy body replaceMap exprToMemRefs in
    StaticAllocLet { args; body }
  | Let { args; body } ->
    let args =
      List.map args ~f:(fun { binding; value } ->
        { binding; value = removeHostToDevCopy value replaceMap exprToMemRefs })
    in
    let body = removeHostToDevCopy body replaceMap exprToMemRefs in
    Let { args; body }
  | Box { indices; body; type' } ->
    let body = removeHostToDevCopy body replaceMap exprToMemRefs in
    Box { indices; body; type' }
  | StaticArrayInit stArrInitVals -> StaticArrayInit stArrInitVals
  | Literal l -> Literal l
  | Values { elements; type' } ->
    let elements =
      List.map elements ~f:(fun e -> removeHostToDevCopy e replaceMap exprToMemRefs)
    in
    Values { elements; type' }
  | ScalarPrimitive { op; args; type' } ->
    let args =
      List.map args ~f:(fun a -> removeHostToDevCopy a replaceMap exprToMemRefs)
    in
    ScalarPrimitive { op; args; type' }
  | TupleDeref { index; tuple; type' } ->
    let tuple = removeHostToDevCopy tuple replaceMap exprToMemRefs in
    TupleDeref { index; tuple; type' }
  | ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' } ->
    let arrayArg = removeHostToDevCopy arrayArg replaceMap exprToMemRefs in
    let indexArg = removeHostToDevCopy indexArg replaceMap exprToMemRefs in
    ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' }
  | IfParallelismHitsCutoff { parallelism; cutoff; then'; else'; type' } ->
    let then' = removeHostToDevCopy then' replaceMap exprToMemRefs in
    let else' = removeHostToDevCopy else' replaceMap exprToMemRefs in
    IfParallelismHitsCutoff { parallelism; cutoff; then'; else'; type' }
  | Eseq { statement; expr; type' } ->
    let statement = removeHostToDevCopyStatement statement replaceMap exprToMemRefs in
    let expr = removeHostToDevCopy expr replaceMap exprToMemRefs in
    Eseq { statement; expr; type' }
  | Getmem { addr; type' } -> Getmem { addr; type' }

and removeHostToDevCopyLoopBlock
  : type i o p e.
    (i, o, p, _, e) loopBlock
    -> (_, _, _) Map.t
    -> Identifier.t list
    -> (i, o, p, _, e) loopBlock
  =
  fun { frameShape
      ; indexMode
      ; mapArgs
      ; mapMemArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; mapResultMemFinal
      ; consumer
      ; type'
      }
      replaceMap
      exprToMemRef ->
  let removedMapArgs, mapArgs =
    List.partition_tf mapArgs ~f:(fun { binding = _; ref = { id; type' = _ } } ->
      Map.mem replaceMap id)
  in
  let exprToMemRefAddition =
    List.map removedMapArgs ~f:(fun { binding; ref = _ } -> binding)
  in
  let exprToMemRef = List.append exprToMemRef exprToMemRefAddition in
  let mapMemArgsAddition =
    removedMapArgs
    |> List.map ~f:(fun { binding; ref = { id; type' = _ } } ->
      let memBinding = binding in
      let mem = Map.find_exn replaceMap id in
      { memBinding; mem })
  in
  let mapMemArgs = List.append mapMemArgs mapMemArgsAddition in
  let mapBody = removeHostToDevCopy mapBody replaceMap exprToMemRef in
  let consumer =
    Maybe.map consumer ~f:(fun c -> removeHostToDevCopyConsumer c replaceMap exprToMemRef)
  in
  { frameShape
  ; indexMode
  ; mapArgs
  ; mapMemArgs
  ; mapIotas
  ; mapBody
  ; mapBodyMatcher
  ; mapResults
  ; mapResultMemFinal
  ; consumer
  ; type'
  }

and removeHostToDevCopyKernel
  { mapResultMemDeviceInterim; loopBlock }
  replaceMap
  exprToMemRefs
  =
  let loopBlock = removeHostToDevCopyLoopBlock loopBlock replaceMap exprToMemRefs in
  { mapResultMemDeviceInterim; loopBlock }

and removeHostToDevCopyStatement
  : type l.
    (l, captures) statement
    -> (_, _, _) Map.t
    -> Identifier.t list
    -> (l, captures) statement
  =
  fun statement replaceMap exprToMemRef ->
  match statement with
  | Putmem { expr; addr; type' } ->
    let expr = removeHostToDevCopy expr replaceMap exprToMemRef in
    Putmem { expr; addr; type' }
  | MapKernel { kernel; captures; blocks; threads } ->
    let kernel = removeHostToDevCopyMapKernel kernel replaceMap exprToMemRef in
    let captures = removeHostToDevCopyCaptures captures replaceMap exprToMemRef in
    MapKernel { kernel; captures; blocks; threads }
  | ComputeForSideEffects expr ->
    let expr = removeHostToDevCopy expr replaceMap exprToMemRef in
    ComputeForSideEffects expr
  | Statements statements ->
    let statements =
      List.map statements ~f:(fun s ->
        removeHostToDevCopyStatement s replaceMap exprToMemRef)
    in
    Statements statements
  | SLet { args; body } ->
    let args =
      List.map args ~f:(fun { binding; value } ->
        { binding; value = removeHostToDevCopy value replaceMap exprToMemRef })
    in
    let body = removeHostToDevCopyStatement body replaceMap exprToMemRef in
    SLet { args; body }
  | SMallocLet { memArgs; body } ->
    let body = removeHostToDevCopyStatement body replaceMap exprToMemRef in
    SMallocLet { memArgs; body }
  | ReifyShapeIndex i -> ReifyShapeIndex i

and removeHostToDevCopyMapKernel
  { label; map; mapResultMemDeviceInterim; mapResultMemHostFinal }
  replaceMap
  exprToMemRefs
  =
  let map = removeHostToDevCopyMapInKernel map replaceMap exprToMemRefs in
  { label; map; mapResultMemDeviceInterim; mapResultMemHostFinal }

and removeHostToDevCopyMapInKernel
  { frameShape; indexMode; mapArgs; mapMemArgs; mapIotas; mapBody; type' }
  replaceMap
  exprToMemRef
  =
  let removedMapArgs, mapArgs =
    List.partition_tf mapArgs ~f:(fun { binding = _; ref = { id; type' = _ } } ->
      Map.mem replaceMap id)
  in
  let mapMemArgsAddition =
    removedMapArgs
    |> List.map ~f:(fun { binding; ref = { id; type' = _ } } ->
      let memBinding = binding in
      let mem = Map.find_exn replaceMap id in
      { memBinding; mem })
  in
  let exprToMemRefAddition =
    List.map removedMapArgs ~f:(fun { binding; ref = _ } -> binding)
  in
  let exprToMemRef = List.append exprToMemRef exprToMemRefAddition in
  let mapMemArgs = List.append mapMemArgs mapMemArgsAddition in
  let mapBody = removeHostToDevCopyMapBody mapBody replaceMap exprToMemRef in
  { frameShape; indexMode; mapArgs; mapMemArgs; mapIotas; mapBody; type' }

and removeHostToDevCopyMapBody mapBody replaceMap exprToMemRef =
  match mapBody with
  | MapBodyStatement statement ->
    MapBodyStatement (removeHostToDevCopyStatement statement replaceMap exprToMemRef)
  | MapBodySubMaps subMaps ->
    let subMaps =
      List.map subMaps ~f:(fun m ->
        removeHostToDevCopyMapInKernel m replaceMap exprToMemRef)
    in
    MapBodySubMaps subMaps

and removeHostToDevCopyConsumer
  : type o i p.
    (o, i, p, captures) consumerOp
    -> (_, _, _) Map.t
    -> Identifier.t list
    -> (o, i, p, captures) consumerOp
  =
  fun consumer replaceMap exprToMemRef ->
  match consumer with
  | ReduceSeq { arg; zero; body; indexMode; d; type' } ->
    let zero = removeHostToDevCopy zero replaceMap exprToMemRef in
    let body = removeHostToDevCopy body replaceMap exprToMemRef in
    ReduceSeq { arg; zero; body; indexMode; d; type' }
  | ReducePar
      { reduce = { arg; zero; body; indexMode; d; type' }
      ; interimResultMemDeviceInterim
      ; interimResultMemHostFinal
      ; outerBody
      } ->
    let zero = removeHostToDevCopy zero replaceMap exprToMemRef in
    let body = removeHostToDevCopy body replaceMap exprToMemRef in
    let reduce : (o, i, _) reduce = { arg; zero; body; indexMode; d; type' } in
    ReducePar
      { reduce; interimResultMemHostFinal; interimResultMemDeviceInterim; outerBody }
  | ScanSeq { arg; zero; body; indexMode; d; scanResultMemFinal; type' } ->
    let zero = removeHostToDevCopy zero replaceMap exprToMemRef in
    let body = removeHostToDevCopy body replaceMap exprToMemRef in
    ScanSeq { arg; zero; body; indexMode; d; scanResultMemFinal; type' }
  | ScanPar
      { scan = { arg; zero; body; indexMode; d; scanResultMemFinal; type' }
      ; scanResultMemDeviceInterim
      } ->
    let zero = removeHostToDevCopy zero replaceMap exprToMemRef in
    let body = removeHostToDevCopy body replaceMap exprToMemRef in
    let scan : (o, i, _) scan =
      { arg; zero; body; indexMode; d; scanResultMemFinal; type' }
    in
    ScanPar { scan; scanResultMemDeviceInterim }
  | Scatter { valuesArg; indicesArg; dIn; dOut; memInterim; memFinal; type' } ->
    Scatter { valuesArg; indicesArg; dIn; dOut; memInterim; memFinal; type' }
  | Fold
      { zeroArg = { zeroBinding; zeroValue }
      ; arrayArgs
      ; mappedMemArgs
      ; reverse
      ; body
      ; d
      ; character
      ; type'
      } ->
    let zeroValue = removeHostToDevCopy zeroValue replaceMap exprToMemRef in
    let zeroArg : (o, _) foldZeroArg = { zeroBinding; zeroValue } in
    let body = removeHostToDevCopy body replaceMap exprToMemRef in
    Fold { zeroArg; arrayArgs; mappedMemArgs; reverse; body; d; character; type' }

and removeHostToDevCopyCaptures
  ({ exprCaptures; indexCaptures; memCaptures } : captures)
  replaceMap
  exprToMemRef
  : captures
  =
  let replaceCaptures, moveCaptures, exprCapturesList =
    exprCaptures
    |> Map.to_alist
    |> List.partition3_map ~f:(fun ((id, _) as capture) ->
      if Map.mem replaceMap id
      then `Fst capture
      else if List.mem exprToMemRef id ~equal:Identifier.equal
      then `Snd capture
      else `Trd capture)
  in
  let exprCaptures = exprCapturesList |> Map.of_alist_exn (module Identifier) in
  let memCapturesAddition =
    replaceCaptures
    |> List.concat_map ~f:(fun (id, _) ->
      let mem = Map.find_exn replaceMap id in
      let captures = findAllCapturesInMem mem in
      List.map captures ~f:(fun { id; type' } -> id, type'))
    |> List.append moveCaptures
    |> Map.of_alist_reduce
         (module Identifier)
         ~f:(fun a b ->
           assert (Acorn.Type.equal a b);
           a)
  in
  let memCaptures =
    Map.merge_skewed memCaptures memCapturesAddition ~combine:(fun ~key:_ v _ -> v)
  in
  { exprCaptures; memCaptures; indexCaptures }

and findAllCapturesInMem (mem : Acorn.Mem.t) : Acorn.Mem.ref list =
  match mem with
  | Acorn.Mem.Ref ref -> [ ref ]
  | Acorn.Mem.TupleDeref { tuple; index = _; type' = _ } -> findAllCapturesInMem tuple
  | Acorn.Mem.Values { elements; type' = _ } ->
    List.concat_map elements ~f:findAllCapturesInMem
  | Acorn.Mem.Index { mem; offset = _; type' = _ } -> findAllCapturesInMem mem
;;

(* -------------------- Rewrite #2 (Elim dev->host) ---------------------- *)
(* This rewrite is only supposed to happen after the first one *)

(* Return a set of all used variables in the given expression *)
let rec findUses : type l. (l, captures) t -> (Identifier.t, _) Set.t = function
  | Ref { id; type' = _ } -> Set.singleton (module Identifier) id
  | BoxValue { box; type' = _ } -> findUses box
  | IndexLet { indexArgs; body; type' = _ } ->
    let argUses =
      List.map indexArgs ~f:(fun { indexBinding = _; indexValue; sort = _ } ->
        match indexValue with
        | Runtime expr -> findUses expr
        | FromBox { box; i = _ } -> findUses box)
    in
    let bodyUses = findUses body in
    Set.union_list (module Identifier) (bodyUses :: argUses)
  | MallocLet { memArgs = _; body } -> findUses body
  | ReifyDimensionIndex _ -> Set.empty (module Identifier)
  | ShapeProd _ -> Set.empty (module Identifier)
  | LoopBlock lb -> findUsesLoopBlock lb
  | LoopKernel
      { kernel = { mapResultMemDeviceInterim = _; loopBlock }
      ; captures
      ; blocks = _
      ; threads = _
      } ->
    let captureUses = findUsesCaptures captures in
    let loopBlockUses = findUsesLoopBlock loopBlock in
    Set.union captureUses loopBlockUses
  | StaticAllocLet {args; body}
  | Let { args; body } ->
    let argsUses = List.map args ~f:(fun { binding = _; value } -> findUses value) in
    let bodyUses = findUses body in
    Set.union_list (module Identifier) (bodyUses :: argsUses)
  | Box { indices = _; body; type' = _ } -> findUses body
  | StaticArrayInit _ -> Set.empty (module Identifier)
  | Literal _ -> Set.empty (module Identifier)
  | Values { elements; type' = _ } ->
    let uses = List.map elements ~f:findUses in
    Set.union_list (module Identifier) uses
  | ScalarPrimitive { op = _; args; type' = _ } ->
    let uses = List.map args ~f:findUses in
    Set.union_list (module Identifier) uses
  | TupleDeref { index = _; tuple; type' = _ } -> findUses tuple
  | ContiguousSubArray
      { arrayArg; indexArg; originalShape = _; resultShape = _; type' = _ } ->
    let arrayUses = findUses arrayArg in
    let indexUses = findUses indexArg in
    Set.union arrayUses indexUses
  | IfParallelismHitsCutoff { parallelism = _; cutoff = _; then'; else'; type' = _ } ->
    let thenUses = findUses then' in
    let elseUses = findUses else' in
    Set.union thenUses elseUses
  | Eseq { statement; expr; type' = _ } ->
    let statementUses = findUsesStatement statement in
    let exprUses = findUses expr in
    Set.union statementUses exprUses
  | Getmem _ -> Set.empty (module Identifier)

and findUsesStatement : type l. (l, captures) statement -> (Identifier.t, _) Set.t
  = function
  | Putmem { expr; addr = _; type' = _ } -> findUses expr
  | MapKernel
      { kernel =
          { label = _; map; mapResultMemDeviceInterim = _; mapResultMemHostFinal = _ }
      ; captures
      ; blocks = _
      ; threads = _
      } ->
    let captureUses = findUsesCaptures captures in
    let mapUses = findUsesMapInKernel map in
    Set.union captureUses mapUses
  | ComputeForSideEffects expr -> findUses expr
  | Statements statements ->
    Set.union_list (module Identifier) (List.map statements ~f:findUsesStatement)
  | SLet { args; body } ->
    let bodyUses = findUsesStatement body in
    let argUses = List.map args ~f:(fun { binding = _; value } -> findUses value) in
    Set.union_list (module Identifier) (bodyUses :: argUses)
  | SMallocLet { memArgs = _; body } -> findUsesStatement body
  | ReifyShapeIndex _ -> Set.empty (module Identifier)

and findUsesLoopBlock
  : type o i p e. (o, i, p, captures, e) loopBlock -> (Identifier.t, _) Set.t
  =
  fun { frameShape = _
      ; indexMode = _
      ; mapArgs
      ; mapMemArgs = _
      ; mapIotas = _
      ; mapBody
      ; mapBodyMatcher = _
      ; mapResults = _
      ; mapResultMemFinal = _
      ; consumer
      ; type' = _
      } ->
  let consumerUsesMaybe = Maybe.map consumer ~f:findUsesConsumer in
  let consumerUses =
    match consumerUsesMaybe with
    | Nothing -> Set.empty (module Identifier)
    | Just uses -> uses
  in
  let mapArgsUses =
    mapArgs
    |> List.map ~f:(fun { binding = _; ref = { id; type' = _ } } -> id)
    |> Set.of_list (module Identifier)
  in
  let mapBodyUses = findUses mapBody in
  Set.union_list (module Identifier) [ consumerUses; mapArgsUses; mapBodyUses ]

and findUsesConsumer : type o i p. (o, i, p, _) consumerOp -> (Identifier.t, _) Set.t
  = function
  | ReduceSeq { arg; zero; body; indexMode = _; d = _; type' = _ } ->
    let argUses = findUsesProduction arg.production in
    let zeroUses = findUses zero in
    let bodyUses = findUses body in
    Set.union_list (module Identifier) [ argUses; zeroUses; bodyUses ]
  | ReducePar
      { reduce = { arg; zero; body; indexMode = _; d = _; type' = _ }
      ; interimResultMemDeviceInterim = _
      ; interimResultMemHostFinal = _
      ; outerBody
      } ->
    let argUses = findUsesProduction arg.production in
    let zeroUses = findUses zero in
    let bodyUses = findUses body in
    let outerBodyUses = findUses outerBody in
    Set.union_list (module Identifier) [ argUses; zeroUses; bodyUses; outerBodyUses ]
  | ScanSeq { arg; zero; body; indexMode = _; d = _; scanResultMemFinal = _; type' = _ }
    ->
    let argUses = findUsesProduction arg.production in
    let zeroUses = findUses zero in
    let bodyUses = findUses body in
    Set.union_list (module Identifier) [ argUses; zeroUses; bodyUses ]
  | ScanPar
      { scan =
          { arg; zero; body; indexMode = _; d = _; scanResultMemFinal = _; type' = _ }
      ; scanResultMemDeviceInterim = _
      } ->
    let argUses = findUsesProduction arg.production in
    let zeroUses = findUses zero in
    let bodyUses = findUses body in
    Set.union_list (module Identifier) [ argUses; zeroUses; bodyUses ]
  | Scatter
      { valuesArg
      ; indicesArg
      ; dIn = _
      ; dOut = _
      ; memInterim = _
      ; memFinal = _
      ; type' = _
      } ->
    Set.of_list (module Identifier) [ valuesArg.productionId; indicesArg.productionId ]
  | Fold
      { zeroArg = { zeroBinding = _; zeroValue }
      ; arrayArgs
      ; mappedMemArgs = _
      ; reverse = _
      ; body = _
      ; d = _
      ; character = _
      ; type' = _
      } ->
    let zeroUses = findUses zeroValue in
    let arrayArgUses =
      List.map
        arrayArgs
        ~f:(fun { binding = _; production = { productionId; type' = _ } } -> productionId)
    in
    let arrayArgUses = Set.of_list (module Identifier) arrayArgUses in
    Set.union zeroUses arrayArgUses

and findUsesMapBody = function
  | MapBodyStatement statement -> findUsesStatement statement
  | MapBodySubMaps subMaps ->
    Set.union_list (module Identifier) (List.map subMaps ~f:findUsesMapInKernel)

and findUsesMapInKernel
  { frameShape = _
  ; indexMode = _
  ; mapArgs
  ; mapMemArgs = _
  ; mapIotas = _
  ; mapBody
  ; type' = _
  }
  =
  let argUses =
    Set.of_list
      (module Identifier)
      (List.map mapArgs ~f:(fun { binding = _; ref = { id; type' = _ } } -> id))
  in
  let bodyUses = findUsesMapBody mapBody in
  Set.union argUses bodyUses

(* and findUsesMapKernel _ = _ *)

and findUsesCaptures { exprCaptures; indexCaptures = _; memCaptures = _ } =
  exprCaptures
  |> Map.to_alist
  |> List.map ~f:(fun (id, _) -> id)
  |> Set.of_list (module Identifier)

and findUsesProduction p =
  match p with
  | ProductionTuple { elements; type' = _ } ->
    Set.union_list (module Identifier) (List.map elements ~f:findUsesProduction)
  | ProductionTupleAtom { productionId; type' = _ } ->
    Set.singleton (module Identifier) productionId
;;

type 'l letBinders =
  | Used of ('l, captures) letArg list
  | Unused of ('l, captures) letArg list
[@@deriving sexp_of]

let generateLetBindersList
  : type l. (l, _) letArg list -> (Identifier.t, _) Set.t -> l letBinders list
  =
  fun args bodyUses ->
  let letBindersList, letArgList, isCollectingUsed =
    List.fold_left
      args
      ~init:([], [], true)
      ~f:(fun (letBindersList, letArgList, isCollectingUsed) { binding; value } ->
        let bindingUsed = Set.mem bodyUses binding in
        match bindingUsed, isCollectingUsed with
        | true, true | false, false ->
          (* just append to letArgList *)
          letBindersList, { binding; value } :: letArgList, isCollectingUsed
        | true, false | false, true ->
          let newLetBinders =
            if isCollectingUsed
            then Used (List.rev letArgList)
            else Unused (List.rev letArgList)
          in
          newLetBinders :: letBindersList, [ { binding; value } ], not isCollectingUsed
        (* create unused list from letArgList, switch to used and append current value *))
  in
  let letBindersList =
    (* letArgList is always going to have at least one element so no need to check that *)
    if isCollectingUsed
    then Used (List.rev letArgList) :: letBindersList
    else Unused (List.rev letArgList) :: letBindersList
  in
  List.rev letBindersList
;;

let rec removeReturnValue : type l. (l, captures) t -> (l, _) statement option =
  fun expr ->
  match expr with
  | Ref _ -> None
  | BoxValue { box; type' = _ } -> removeReturnValue box
  | IndexLet let' -> Some (ComputeForSideEffects (IndexLet let'))
  | MallocLet { memArgs; body } ->
    let body = removeReturnValue body |> Option.value ~default:(Statements []) in
    Some (SMallocLet { memArgs; body })
  | ReifyDimensionIndex _ -> None
  | ShapeProd _ -> None
  | LoopBlock lb -> Some (ComputeForSideEffects (LoopBlock lb))
  | LoopKernel
      { kernel =
          { mapResultMemDeviceInterim
          ; loopBlock =
              { frameShape
              ; indexMode
              ; mapArgs
              ; mapMemArgs
              ; mapIotas
              ; mapBody
              ; mapBodyMatcher
              ; mapResults
              ; mapResultMemFinal = _
              ; consumer
              ; type' = _
              }
          }
      ; captures
      ; blocks
      ; threads
      } ->
    let mapResultMemFinal =
      Acorn.Mem.Values { elements = []; type' = Acorn.Type.Tuple [] }
    in
    let consumer = Maybe.map consumer ~f:removeReturnValueConsumer in
    let type' = [ Acorn.Type.Tuple []; Acorn.Type.Tuple [] ] in
    let loopBlock =
      { frameShape
      ; indexMode
      ; mapArgs
      ; mapMemArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; mapResultMemFinal
      ; consumer
      ; type'
      }
    in
    let kernel = { mapResultMemDeviceInterim; loopBlock } in
    Some (ComputeForSideEffects (LoopKernel { kernel; captures; blocks; threads }))
  | StaticAllocLet { args; body }
  | Let { args; body } ->
    let bodyUses = findUses body in
    let body = body |> removeReturnValue |> Option.value ~default:(Statements []) in
    let letBinders = generateLetBindersList args bodyUses in
    let rec generateNewExpr letBindersList =
      match letBindersList with
      | [] -> body
      | hd :: tl ->
        let body = generateNewExpr tl in
        (match hd with
         | Used args -> SLet { args; body }
         | Unused exprs ->
           let exprs = List.map exprs ~f:(fun { binding = _; value } -> value) in
           let statements = List.filter_map exprs ~f:removeReturnValue in
           let statements = List.rev (body :: statements) in
           Statements statements)
    in
    Some (generateNewExpr letBinders)
  | Box { indices = _; body; type' = _ } ->
    let body = removeReturnValue body in
    (match body with
     | None -> None
     | Some v -> Some v)
  | StaticArrayInit _ -> None
  | Literal _ -> None
  | Values { elements; type' = _ } ->
    let elements =
      elements
      |> List.map ~f:(fun e -> removeReturnValue e)
      |> List.filter ~f:Option.is_some
    in
    if List.is_empty elements
    then None
    else
      Some
        (Statements
           (List.concat_map elements ~f:(function
             | None -> []
             | Some s -> [ s ])))
  | ScalarPrimitive { op = _; args; type' = _ } ->
    let args = List.filter_map args ~f:removeReturnValue in
    Some (Statements args)
  | TupleDeref { index = _; tuple; type' = _ } -> removeReturnValue tuple
  | ContiguousSubArray
      { arrayArg; indexArg; originalShape = _; resultShape = _; type' = _ } ->
    let arrayArg = removeReturnValue arrayArg in
    let arrayArg = Option.value arrayArg ~default:(Statements []) in
    let indexArg = removeReturnValue indexArg in
    let indexArg = Option.value indexArg ~default:(Statements []) in
    Some (Statements [ arrayArg; indexArg ])
  | IfParallelismHitsCutoff { parallelism; cutoff; then'; else'; type' } ->
    Some
      (ComputeForSideEffects
         (IfParallelismHitsCutoff { parallelism; cutoff; then'; else'; type' }))
  | Eseq { statement; expr; type' = _ } ->
    let statement = removeReturnValueStatement statement in
    let expr = removeReturnValue expr in
    let expr =
      match expr with
      | None -> []
      | Some v -> [ v ]
    in
    Some (Statements (statement :: expr))
  | Getmem _ -> None

and removeReturnValueStatement : type l. (l, _) statement -> (l, _) statement =
  fun statement ->
  match statement with
  | Putmem { expr; addr; type' } -> Putmem { expr; addr; type' }
  | MapKernel
      { kernel = { label; map; mapResultMemDeviceInterim; mapResultMemHostFinal = _ }
      ; captures
      ; blocks
      ; threads
      } ->
    let mapResultMemHostFinal =
      Acorn.Mem.Values { elements = []; type' = Acorn.Type.Tuple [] }
    in
    let kernel = { label; map; mapResultMemDeviceInterim; mapResultMemHostFinal } in
    MapKernel { kernel; captures; blocks; threads }
  | ComputeForSideEffects expr ->
    (match removeReturnValue expr with
     | None -> Statements []
     | Some s -> s)
  | Statements statements ->
    let statements = List.map statements ~f:(fun s -> removeReturnValueStatement s) in
    Statements statements
  | SLet { args; body } ->
    let bodyUses = findUsesStatement body in
    let body = removeReturnValueStatement body in
    let letBinders = generateLetBindersList args bodyUses in
    let rec generateNewExpr letBindersList =
      match letBindersList with
      | [] -> body
      | hd :: tl ->
        let body = generateNewExpr tl in
        (match hd with
         | Used args -> SLet { args; body }
         | Unused exprs ->
           let exprs = List.map exprs ~f:(fun { binding = _; value } -> value) in
           let statements = List.filter_map exprs ~f:removeReturnValue in
           let statements = List.rev (body :: statements) in
           Statements statements)
    in
    generateNewExpr letBinders
  | SMallocLet { memArgs; body } ->
    let body = removeReturnValueStatement body in
    SMallocLet { memArgs; body }
  | ReifyShapeIndex i -> ReifyShapeIndex i

and removeReturnValueConsumer
  : type o i p. (o, i, p, _) consumerOp -> (o, i, p, _) consumerOp
  =
  fun consumer ->
  match consumer with
  | ScanPar
      { scan = { arg; zero; body; indexMode; d; scanResultMemFinal = _; type' }
      ; scanResultMemDeviceInterim
      } ->
    let scanResultMemFinal =
      Acorn.Mem.Values { elements = []; type' = Acorn.Type.Tuple [] }
    in
    let scan = { arg; zero; body; indexMode; d; scanResultMemFinal; type' } in
    ScanPar { scan; scanResultMemDeviceInterim }
  | ReducePar
      { reduce; interimResultMemDeviceInterim; interimResultMemHostFinal = _; outerBody }
    ->
    let interimResultMemHostFinal = None in
    ReducePar
      { reduce; interimResultMemDeviceInterim; interimResultMemHostFinal; outerBody }
  | other -> other

and getNewFinalMem (hostMem : Acorn.Mem.t) (devMem : Acorn.Mem.t) ~memId
  : Acorn.Mem.t option
  =
  match hostMem, devMem with
  | Ref hostId, Ref devId ->
    if Identifier.equal memId devId.id then None else Some (Ref hostId)
  | Values hostVals, Values devVals
    when List.length hostVals.elements = List.length devVals.elements ->
    let newElements =
      List.map2_exn hostVals.elements devVals.elements ~f:(getNewFinalMem ~memId)
    in
    if List.for_all newElements ~f:Option.is_none then None else Some (Values hostVals)
  | TupleDeref hostDeref, TupleDeref devDeref when hostDeref.index = devDeref.index ->
    (* Values case should reconstruct the TupleDeref because *)
    let finalMem = getNewFinalMem hostDeref.tuple devDeref.tuple ~memId in
    (match finalMem with
     | None -> None
     | Some _ -> Some (TupleDeref hostDeref))
  | Index hostIndex, Index devIndex
    when Acorn.Index.equal_dimension hostIndex.offset devIndex.offset ->
    let finalMem = getNewFinalMem hostIndex.mem devIndex.mem ~memId in
    (match finalMem with
     | None -> None
     | Some _ -> Some (Index hostIndex))
  | hostMem, _ -> Some hostMem
;;

let rec removeDevToHostCopy : type l. (l, _) t -> replaceMap:(_, _, _) Map.t -> (l, _) t =
  fun expr ~replaceMap ->
  match expr with
  | Ref r -> Ref r
  | BoxValue { box; type' } ->
    let box = removeDevToHostCopy box ~replaceMap in
    BoxValue { box; type' }
  | IndexLet { indexArgs; body; type' } ->
    let body = removeDevToHostCopy body ~replaceMap in
    let indexArgs =
      List.map indexArgs ~f:(fun { indexBinding; indexValue; sort } ->
        let indexValue =
          match indexValue with
          | Runtime expr -> Runtime (removeDevToHostCopy expr ~replaceMap)
          | FromBox { box; i } ->
            let box = removeDevToHostCopy box ~replaceMap in
            FromBox { box; i }
        in
        { indexBinding; indexValue; sort })
    in
    IndexLet { indexArgs; body; type' }
  | MallocLet { memArgs; body } ->
    let body = removeDevToHostCopy body ~replaceMap in
    MallocLet { body; memArgs }
  | ReifyDimensionIndex i -> ReifyDimensionIndex i
  | ShapeProd p -> ShapeProd p
  | LoopBlock
      { frameShape
      ; indexMode
      ; mapArgs
      ; mapMemArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; mapResultMemFinal
      ; consumer
      ; type'
      } ->
    let mapBody = removeDevToHostCopy mapBody ~replaceMap in
    let consumer = Maybe.map consumer ~f:(removeDevToHostCopyConsumer ~replaceMap) in
    LoopBlock
      { frameShape
      ; indexMode
      ; mapArgs
      ; mapMemArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; mapResultMemFinal
      ; consumer
      ; type'
      }
  | LoopKernel kernel -> LoopKernel kernel
  | StaticAllocLet { args; body } ->
    let body = removeDevToHostCopy body ~replaceMap in
    StaticAllocLet { args; body }
  | Let { args; body } ->
    let bodyUses = findUses body in
    let rec generateNewExpr letBindersList =
      match letBindersList with
      | [] -> removeDevToHostCopy body ~replaceMap
      | hd :: tl ->
        let body = generateNewExpr tl in
        (match hd with
         | Used args -> Let { args; body }
         | Unused exprs ->
           let statement =
             Statements
               (List.concat_map exprs ~f:(fun { binding = _; value } ->
                  let value = removeReturnValue value in
                  match value with
                  | None -> []
                  | Some s -> [ s ]))
           in
           let type' = type' body in
           Eseq { statement; expr = body; type' })
    in
    let letBindersList = generateLetBindersList args bodyUses in
    generateNewExpr letBindersList
  | Box { indices; body; type' } ->
    let body = removeDevToHostCopy body ~replaceMap in
    Box { indices; body; type' }
  | StaticArrayInit stArrInitVals -> StaticArrayInit stArrInitVals  
  | Literal l -> Literal l
  | Values { elements; type' } ->
    let elements = List.map elements ~f:(removeDevToHostCopy ~replaceMap) in
    Values { elements; type' }
  | ScalarPrimitive { op; args; type' } ->
    let args = List.map args ~f:(removeDevToHostCopy ~replaceMap) in
    ScalarPrimitive { args; op; type' }
  | TupleDeref { index; tuple; type' } ->
    let tuple = removeDevToHostCopy tuple ~replaceMap in
    TupleDeref { tuple; index; type' }
  | ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' } ->
    let arrayArg = removeDevToHostCopy arrayArg ~replaceMap in
    let indexArg = removeDevToHostCopy indexArg ~replaceMap in
    ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' }
  | IfParallelismHitsCutoff { parallelism; cutoff; then'; else'; type' } ->
    let then' = removeDevToHostCopy then' ~replaceMap in
    let else' = removeDevToHostCopy else' ~replaceMap in
    IfParallelismHitsCutoff { parallelism; cutoff; then'; else'; type' }
  | Eseq { statement; expr; type' } ->
    let statement = removeDevToHostCopyStatement statement ~replaceMap in
    let expr = removeDevToHostCopy expr ~replaceMap in
    Eseq { statement; expr; type' }
  | Getmem m -> Getmem m

and removeDevToHostCopyStatement
  : type l.
    (l, captures) statement -> replaceMap:(_, _, _) Map.t -> (l, captures) statement
  =
  fun statement ~replaceMap ->
  match statement with
  | Putmem { expr; addr; type' } ->
    let expr = removeDevToHostCopy expr ~replaceMap in
    Putmem { expr; addr; type' }
  | MapKernel mapKernel -> MapKernel mapKernel
  | ComputeForSideEffects expr ->
    ComputeForSideEffects (removeDevToHostCopy expr ~replaceMap)
  | Statements statements ->
    let statements = List.map statements ~f:(removeDevToHostCopyStatement ~replaceMap) in
    Statements statements
  | SLet { args; body } ->
    let bodyUses = findUsesStatement body in
    let rec generateNewExpr letBindersList =
      match letBindersList with
      | [] -> body
      | hd :: tl ->
        let body = generateNewExpr tl in
        (match hd with
         | Used args -> SLet { args; body }
         | Unused exprs ->
           let statements =
             List.concat_map exprs ~f:(fun { binding = _; value } ->
               let value = removeReturnValue value in
               match value with
               | None -> []
               | Some s -> [ s ])
           in
           let statements = List.rev (body :: statements) in
           Statements statements)
    in
    let letBindersList = generateLetBindersList args bodyUses in
    generateNewExpr letBindersList
  | SMallocLet { memArgs; body } ->
    let body = removeDevToHostCopyStatement body ~replaceMap in
    SMallocLet { memArgs; body }
  | ReifyShapeIndex i -> ReifyShapeIndex i

and removeDevToHostCopyConsumer
  : type o i p.
    (o, i, p, _) consumerOp -> replaceMap:(_, _, _) Map.t -> (o, i, p, _) consumerOp
  =
  fun consumer ~replaceMap ->
  match consumer with
  | ReduceSeq { arg; zero; body; indexMode; d; type' } ->
    let zero = removeDevToHostCopy zero ~replaceMap in
    let body = removeDevToHostCopy body ~replaceMap in
    ReduceSeq { arg; zero; body; indexMode; d; type' }
  | ReducePar
      { reduce = { arg; zero; body; indexMode; d; type' }
      ; interimResultMemDeviceInterim
      ; interimResultMemHostFinal
      ; outerBody
      } ->
    let zero = removeDevToHostCopy zero ~replaceMap in
    let body = removeDevToHostCopy body ~replaceMap in
    let reduce : (_, _, _) reduce = { arg; zero; body; indexMode; d; type' } in
    ReducePar
      { reduce; interimResultMemHostFinal; interimResultMemDeviceInterim; outerBody }
  | ScanSeq { arg; zero; body; indexMode; d; scanResultMemFinal; type' } ->
    let zero = removeDevToHostCopy zero ~replaceMap in
    let body = removeDevToHostCopy body ~replaceMap in
    ScanSeq { arg; zero; body; indexMode; d; scanResultMemFinal; type' }
  | ScanPar
      { scan = { arg; zero; body; indexMode; d; scanResultMemFinal; type' }
      ; scanResultMemDeviceInterim
      } ->
    let zero = removeDevToHostCopy zero ~replaceMap in
    let body = removeDevToHostCopy body ~replaceMap in
    let scan : (_, _, _) scan =
      { arg; zero; body; indexMode; d; scanResultMemFinal; type' }
    in
    ScanPar { scan; scanResultMemDeviceInterim }
  | Scatter s -> Scatter s
  | Fold
      { zeroArg = { zeroBinding; zeroValue }
      ; arrayArgs
      ; mappedMemArgs
      ; reverse
      ; body
      ; d
      ; character
      ; type'
      } ->
    let zeroValue = removeDevToHostCopy zeroValue ~replaceMap in
    let zeroArg : (_, _) foldZeroArg = { zeroBinding; zeroValue } in
    Fold { zeroArg; arrayArgs; mappedMemArgs; reverse; body; d; character; type' }
;;

(* -------------------- Main --------------------- *)
let removeMemMoves expr =
  let open State in
  let infoMap, _ = constructDataFlowMap expr in
  infoMap
  |> Map.to_alist ?key_order:None
  |> List.map ~f:(fun (k, v) ->
    Printf.sprintf
      "  %s - %s\n"
      (Identifier.show k)
      (Sexp.to_string_hum (sexp_of_dfValue v)))
  |> String.concat
  |> Printf.sprintf "Information map: \n%s"
  |> Stdio.prerr_endline;
  let replaceMap = constructReplaceMap expr infoMap in
  let expr = removeHostToDevCopy expr replaceMap [] in
  replaceMap
  |> Map.to_alist ?key_order:None
  |> List.map ~f:(fun (k, v) ->
    Printf.sprintf
      "  %s - %s\n"
      (Identifier.show k)
      (Sexp.to_string_hum ([%sexp_of: Acorn.Mem.t] v)))
  |> String.concat
  |> Printf.sprintf "Replace map: \n%s"
  |> Stdio.prerr_endline;
  let expr = removeDevToHostCopy expr ~replaceMap in
  return expr
;;

module Stage (SB : Source.BuilderT) = struct
  type state = CompilerState.state
  type input = Acorn.withCaptures
  type output = Acorn.withCaptures
  type error = (SB.source option, string) Source.annotate

  let name = "Remove unneeded host-device and device-host memory moves"

  let run input =
    CompilerPipeline.S.make ~f:(fun inputState ->
      State.run (removeMemMoves input) inputState)
  ;;
end
