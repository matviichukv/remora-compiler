open! Base

type dfValue =
  | DFTuple of dfValue list
  | DFRef of Identifier.t (* alias for a different thing *)
  | DFComputedValue
  | DFMem of Acorn.Expr.mallocLoc
  | DFHostToDeviceCopy of dfValue
  | DFDeviceToHostCopy of dfValue
  | DFIterateOver of dfValue
  | DFDeref of
      { index : int
      ; tuple : dfValue
      }
[@@deriving sexp_of]

let constructDataFlowMap (expr : Acorn.Expr.captures Acorn.t) =
  let rec constructDataFlowMapConsumer
    : type o i p.
      (o, i, p, Acorn.Expr.captures) Acorn.Expr.consumerOp
      -> (Identifier.t, dfValue, _) Map.t
      -> (Identifier.t, dfValue, _) Map.t * dfValue
    =
    fun consumer map ->
    match consumer with
    | Acorn.Expr.ReducePar
        { reduce =
            { arg = { firstBinding; secondBinding; production }
            ; zero
            ; body
            ; indexMode = _
            ; d = _
            ; type' = _
            }
        ; interimResultMemDeviceInterim = _
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
      map, value
    | Acorn.Expr.ScanPar
        { scan =
            { arg = { firstBinding; secondBinding; production }
            ; zero
            ; body
            ; indexMode = _
            ; d = _
            ; scanResultMemFinal
            ; type' = _
            }
        ; scanResultMemDeviceInterim = _
        } ->
      let productionValue = productionToDF production in
      let map = Map.update map firstBinding ~f:(fun _ -> DFIterateOver productionValue) in
      let map =
        Map.update map secondBinding ~f:(fun _ -> DFIterateOver productionValue)
      in
      let map, _ = constructDataFlowMap zero map in
      let map, _ = constructDataFlowMap body map in
      map, memToDF scanResultMemFinal
    | Acorn.Expr.ReduceSeq
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
      let map, _ = constructDataFlowMap body map in
      map, DFComputedValue
    | Acorn.Expr.ScanSeq
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
    | Acorn.Expr.Scatter _ -> map, DFComputedValue
    | Acorn.Expr.Fold
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
        | Acorn.Expr.Fold -> DFComputedValue
        | Acorn.Expr.Trace mem -> memToDF mem
      in
      map, value
  and constructDataFlowMapLoopBlock
    : type o i p e.
      (o, i, p, _, e) Acorn.Expr.loopBlock
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
        List.map mapArgs ~f:(fun { binding; ref = { id; type' = _ } } ->
          binding, DFIterateOver (DFRef id))
      in
      let memArgsDF =
        List.map mapMemArgs ~f:(fun { memBinding; mem } -> memBinding, memToDF mem)
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
    : type i p e.
      (i, Acorn.Expr.captures) Acorn.Expr.t
      -> (_, _, _) Map.t
      -> (_, _, _) Map.t * dfValue
    =
    fun expr map ->
    match expr with
    | Ref { id; type' = _ } -> map, DFRef id
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
        { kernel = { mapResultMemDeviceInterim = _; loopBlock }
        ; captures = { exprCaptures; indexCaptures = _; memCaptures }
        ; blocks = _
        ; threads = _
        } ->
      let captureMap =
        List.fold
          (Map.keys exprCaptures @ Map.keys memCaptures)
          ~init:map
          ~f:(fun map id ->
            Map.update map id ~f:(function
              | None -> DFHostToDeviceCopy (DFRef id)
              | Some value -> DFHostToDeviceCopy value))
      in
      let loopBlockMap, loopBlockValue =
        constructDataFlowMapLoopBlock loopBlock captureMap
      in
      loopBlockMap, DFDeviceToHostCopy loopBlockValue
    | Let { args; body } ->
      let newMap =
        List.fold args ~init:map ~f:(fun acc { binding; value } ->
          let _, value = constructDataFlowMap value map in
          Map.update acc binding ~f:(fun _ -> value))
      in
      let bodyMap, body = constructDataFlowMap body newMap in
      bodyMap, body
      (* While indices contain technically speaking arbitrary expressions, *)
      (* none of the expression that *will* end up there are interesting *)
    | Box { indices = _; body; type' = _ } -> constructDataFlowMap body map
    | Literal _ -> map, DFComputedValue
    | Values { elements; type' = _ } ->
      let values, map =
        List.fold elements ~init:([], map) ~f:(fun (vals, map) e ->
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
  and constructDataFlowMapMapInKernel (mapInKernel : _ Acorn.Expr.mapInKernel) map =
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
        List.fold mapArgs ~init:map ~f:(fun map { binding; ref = { id; type' = _ } } ->
          Map.update map binding ~f:(fun _ -> DFRef id))
      in
      let map =
        List.fold mapMemArgs ~init:map ~f:(fun map { memBinding; mem } ->
          Map.update map memBinding ~f:(fun _ -> memToDF mem))
      in
      (match mapBody with
       | Acorn.Expr.MapBodyStatement statement ->
         constructDataFlowMapStatement statement map
       | Acorn.Expr.MapBodySubMaps subMapList ->
         List.fold subMapList ~init:map ~f:(fun map submap ->
           constructDataFlowMapMapInKernel submap map))
  and constructDataFlowMapStatement
    : type i.
      (i, Acorn.Expr.captures) Acorn.Expr.statement -> (_, _, _) Map.t -> (_, _, _) Map.t
    =
    fun statement map ->
    match statement with
    | Acorn.Expr.Putmem _ -> map
    | Acorn.Expr.MapKernel
        { kernel =
            { map = kernelMap; mapResultMemDeviceInterim = _; mapResultMemHostFinal }
        ; captures = { exprCaptures; indexCaptures = _; memCaptures }
        ; blocks = _
        ; threads = _
        } ->
      let map =
        List.fold
          (Map.keys exprCaptures @ Map.keys memCaptures)
          ~init:map
          ~f:(fun map id ->
            Map.update map id ~f:(function
              | None -> DFHostToDeviceCopy (DFRef id)
              | Some value -> DFHostToDeviceCopy value))
      in
      let map = constructDataFlowMapMapInKernel kernelMap map in
      let rec memToDFCopy (mem : Acorn.Mem.t) map =
        match mem with
        | Acorn.Mem.Ref { id; type' = _ } ->
          Map.update map id ~f:(function
            | Some v -> DFDeviceToHostCopy v
            | None -> DFDeviceToHostCopy (DFRef id))
        | Acorn.Mem.Values { elements; type' = _ } ->
          List.fold elements ~init:map ~f:(fun map e -> memToDFCopy e map)
        | Acorn.Mem.Index { mem; offset = _; type' = _ } -> memToDFCopy mem map
        | Acorn.Mem.TupleDeref _ -> raise Unreachable.default
      in
      let map = memToDFCopy mapResultMemHostFinal map in
      (* let finalMemId = *)
      (*   match mapResultMemHostFinal with *)
      (*   | Ref { id; type' = _ } -> id *)
      (*   | _ -> raise Unreachable.default *)
      (* in *)
      (* let map = *)
      (*   Map.update map finalMemId ~f:(fun _ -> DFDeviceToHostCopy (DFRef finalMemId)) *)
      (* in *)
      map
    | Acorn.Expr.ComputeForSideEffects expr ->
      let map, _ = constructDataFlowMap expr map in
      map
    | Acorn.Expr.Statements statements ->
      List.fold statements ~init:map ~f:(fun acc s -> constructDataFlowMapStatement s acc)
    | Acorn.Expr.SLet { args; body } ->
      let map =
        List.fold args ~init:map ~f:(fun acc { binding; value } ->
          let map, value = constructDataFlowMap value acc in
          Map.update map binding ~f:(fun _ -> value))
      in
      constructDataFlowMapStatement body map
    | Acorn.Expr.SMallocLet { memArgs; body } ->
      let map =
        List.fold memArgs ~init:map ~f:(fun map { memBinding; memType = _; memLoc } ->
          Map.update map memBinding ~f:(fun _ -> DFMem memLoc))
      in
      constructDataFlowMapStatement body map
    | Acorn.Expr.ReifyShapeIndex _ -> map
  and memToDF addr =
    match addr with
    | Acorn.Mem.Ref { id; type' = _ } -> DFRef id
    | Acorn.Mem.TupleDeref { tuple; index; type' = _ } ->
      let tuple = memToDF tuple in
      DFDeref { index; tuple }
    | Acorn.Mem.Values { elements; type' = _ } -> DFTuple (List.map elements ~f:memToDF)
    | Acorn.Mem.Index { mem; offset = _; type' = _ } -> memToDF mem
  and productionToDF prod =
    match prod with
    | ProductionTuple { elements; type' = _ } ->
      DFTuple (List.map elements ~f:productionToDF)
    | ProductionTupleAtom { productionId; type' = _ } -> DFRef productionId
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

(* let constructRemoveInfo expr dataFlowMap = raise Unimplemented.default *)

(* let collectInfo expr = *)
(*   let dataFlowMap = constructDataFlowMap expr in *)
(*   constructRemoveInfo expr dataFlowMap *)
(* ;; *)

(* let rewrite expr replaceMap bindingsToRemove = *)
(*   (\* NOTE: correctly modify the captures based on the information so it's in sync *\) *)
(*   raise Unimplemented.default *)
(* ;; *)

(* let removeMemMoves *)
(*   :  Acorn.withCaptures Acorn.t *)
(*   -> (CompilerState.state, Acorn.withCaptures Acorn.t, _) State.t *)
(*   = *)
(*   fun expr -> *)
(*   let (exprReplaceMap, bindingsToRemove) *)
(*         : (Identifier.t, _, _) Map.t * (Acorn.withCaptures Acorn.t, _) Set.t *)
(*     = *)
(*     collectInfo expr *)
(*   in *)
(*   let newExpr = rewrite expr exprReplaceMap bindingsToRemove in *)
(*   newExpr *)
(* ;; *)

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
  |> Stdio.print_endline;
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
