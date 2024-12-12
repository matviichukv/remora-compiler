open! Base
open Acorn.Expr

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
      { kernel = { mapResultMemDeviceInterim; loopBlock }
      ; captures
      ; blocks = _
      ; threads = _
      } ->
    let captureUses = findUsesCaptures captures in
    let loopBlockUses = findUsesLoopBlock loopBlock in
    Set.union
      (Set.union captureUses loopBlockUses)
      (Set.of_list (module Identifier) (findUsesMem mapResultMemDeviceInterim))
  | Let { args; body } ->
    let argsUses = List.map args ~f:(fun { binding = _; value } -> findUses value) in
    let bodyUses = findUses body in
    Set.union_list (module Identifier) (bodyUses :: argsUses)
  | Box { indices = _; body; type' = _ } -> findUses body
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
  | Getmem { addr; type' = _ } -> Set.of_list (module Identifier) (findUsesMem addr)

and findUsesStatement : type l. (l, captures) statement -> (Identifier.t, _) Set.t
  = function
  | Putmem { expr; addr; type' = _ } ->
    Set.union (findUses expr) (Set.of_list (module Identifier) (findUsesMem addr))
  | MapKernel
      { kernel = { label = _; map; mapResultMemDeviceInterim; mapResultMemHostFinal }
      ; captures
      ; blocks = _
      ; threads = _
      } ->
    let captureUses = findUsesCaptures captures in
    let mapUses = findUsesMapInKernel map in
    let deviceMemUses =
      Set.of_list (module Identifier) (findUsesMem mapResultMemDeviceInterim)
    in
    let hostMemUses =
      Set.of_list (module Identifier) (findUsesMem mapResultMemHostFinal)
    in
    Set.union_list
      (module Identifier)
      [ captureUses; mapUses; deviceMemUses; hostMemUses ]
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
      ; mapMemArgs
      ; mapIotas = _
      ; mapBody
      ; mapBodyMatcher = _
      ; mapResults = _
      ; mapResultMemFinal
      ; consumer
      ; type' = _
      } ->
  let consumerUsesMaybe = Maybe.map consumer ~f:findUsesConsumer in
  let consumerUses =
    match consumerUsesMaybe with
    | Nothing -> Set.empty (module Identifier)
    | Just uses -> uses
  in
  let mapBodyUses = findUses mapBody in
  (* args are only used if their 'binding' is used *)
  let mapArgsUses =
    mapArgs
    |> List.filter_map ~f:(fun { binding; ref = { id; type' = _ } } ->
      if Set.mem mapBodyUses binding then Some id else None)
    |> Set.of_list (module Identifier)
  in
  let mapMemArgsUses =
    mapMemArgs
    |> List.concat_map ~f:(fun { memBinding; mem } ->
      if Set.mem mapBodyUses memBinding then findUsesMem mem else [])
    |> Set.of_list (module Identifier)
  in
  let memFinal = Set.of_list (module Identifier) (findUsesMem mapResultMemFinal) in
  Set.union_list
    (module Identifier)
    [ consumerUses; mapArgsUses; mapMemArgsUses; mapBodyUses; memFinal ]

and findUsesMem mem =
  match mem with
  | Acorn.Mem.Ref { id; type' = _ } -> [ id ]
  | Acorn.Mem.TupleDeref { tuple; index = _; type' = _ } -> findUsesMem tuple
  | Acorn.Mem.Values { elements; type' = _ } -> List.concat_map elements ~f:findUsesMem
  | Acorn.Mem.Index { mem; offset = _; type' = _ } -> findUsesMem mem

and findUsesConsumer : type o i p. (o, i, p, _) consumerOp -> (Identifier.t, _) Set.t
  = function
  | ReduceSeq { arg; zero; body; indexMode = _; d = _; type' = _ } ->
    let argUses = findUsesProduction arg.production in
    let zeroUses = findUses zero in
    let bodyUses = findUses body in
    Set.union_list (module Identifier) [ argUses; zeroUses; bodyUses ]
  | ReducePar
      { reduce = { arg; zero; body; indexMode = _; d = _; type' = _ }
      ; interimResultMemDeviceInterim
      ; interimResultMemHostFinal
      ; outerBody
      } ->
    let argUses = findUsesProduction arg.production in
    let zeroUses = findUses zero in
    let bodyUses = findUses body in
    let outerBodyUses = findUses outerBody in
    let deviceMemUses =
      Set.of_list (module Identifier) (findUsesMem interimResultMemDeviceInterim)
    in
    let hostMemUses =
      match interimResultMemHostFinal with
      | Some interimResultMemHostFinal ->
        Set.of_list (module Identifier) (findUsesMem interimResultMemHostFinal)
      | None -> Set.empty (module Identifier)
    in
    Set.union_list
      (module Identifier)
      [ argUses; zeroUses; bodyUses; outerBodyUses; deviceMemUses; hostMemUses ]
  | ScanSeq { arg; zero; body; indexMode = _; d = _; scanResultMemFinal; type' = _ } ->
    let argUses = findUsesProduction arg.production in
    let zeroUses = findUses zero in
    let bodyUses = findUses body in
    let finalMemUses = Set.of_list (module Identifier) (findUsesMem scanResultMemFinal) in
    Set.union_list (module Identifier) [ argUses; zeroUses; bodyUses; finalMemUses ]
  | ScanPar
      { scan = { arg; zero; body; indexMode = _; d = _; scanResultMemFinal; type' = _ }
      ; scanResultMemDeviceInterim
      } ->
    let argUses = findUsesProduction arg.production in
    let zeroUses = findUses zero in
    let bodyUses = findUses body in
    let finalMemUses = Set.of_list (module Identifier) (findUsesMem scanResultMemFinal) in
    let deviceMemUses =
      Set.of_list (module Identifier) (findUsesMem scanResultMemDeviceInterim)
    in
    Set.union_list
      (module Identifier)
      [ argUses; zeroUses; bodyUses; finalMemUses; deviceMemUses ]
  | Scatter { valuesArg; indicesArg; dIn = _; dOut = _; memInterim; memFinal; type' = _ }
    ->
    let finalMemUses = Set.of_list (module Identifier) (findUsesMem memFinal) in
    let deviceMemUses = Set.of_list (module Identifier) (findUsesMem memInterim) in
    let productionUses =
      Set.of_list (module Identifier) [ valuesArg.productionId; indicesArg.productionId ]
    in
    Set.union_list (module Identifier) [ finalMemUses; deviceMemUses; productionUses ]
  | Fold
      { zeroArg = { zeroBinding = _; zeroValue }
      ; arrayArgs
      ; mappedMemArgs
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
    let memArgsUses =
      mappedMemArgs
      |> List.concat_map ~f:(fun { memBinding = _; mem } -> findUsesMem mem)
      |> Set.of_list (module Identifier)
    in
    Set.union_list (module Identifier) [ zeroUses; arrayArgUses; memArgsUses ]

and findUsesMapBody = function
  | MapBodyStatement statement -> findUsesStatement statement
  | MapBodySubMaps subMaps ->
    Set.union_list (module Identifier) (List.map subMaps ~f:findUsesMapInKernel)

and findUsesMapInKernel
  { frameShape = _; indexMode = _; mapArgs; mapMemArgs; mapIotas = _; mapBody; type' = _ }
  =
  let bodyUses = findUsesMapBody mapBody in
  let argUses =
    mapArgs
    |> List.filter_map ~f:(fun { binding; ref = { id; type' = _ } } ->
      if Set.mem bodyUses binding then Some id else None)
    |> Set.of_list (module Identifier)
  in
  let mapMemArgsUses =
    mapMemArgs
    |> List.concat_map ~f:(fun { memBinding; mem } ->
      if Set.mem bodyUses memBinding then findUsesMem mem else [])
    |> Set.of_list (module Identifier)
  in
  Set.union_list (module Identifier) [ argUses; bodyUses; mapMemArgsUses ]

(* and findUsesMapKernel _ = _ *)

and findUsesCaptures { exprCaptures; indexCaptures = _; memCaptures } =
  let exprUses =
    exprCaptures
    |> Map.to_alist
    |> List.map ~f:(fun (id, _) -> id)
    |> Set.of_list (module Identifier)
  in
  let memUses =
    memCaptures
    |> Map.to_alist
    |> List.map ~f:(fun (id, _) -> id)
    |> Set.of_list (module Identifier)
  in
  Set.union exprUses memUses

and findUsesProduction p =
  match p with
  | ProductionTuple { elements; type' = _ } ->
    Set.union_list (module Identifier) (List.map elements ~f:findUsesProduction)
  | ProductionTupleAtom { productionId; type' = _ } ->
    Set.singleton (module Identifier) productionId
;;

let rec rewriteWithoutUnusedVars
  : type l.
    (l, captures) Acorn.Expr.t -> (Identifier.t, _) Set.t -> (l, captures) Acorn.Expr.t
  =
  fun expr uses ->
  match expr with
  | Ref r -> Ref r
  | BoxValue { box; type' } ->
    let box = rewriteWithoutUnusedVars box uses in
    BoxValue { box; type' }
  | IndexLet { indexArgs; body; type' } ->
    let body = rewriteWithoutUnusedVars body uses in
    IndexLet { indexArgs; body; type' }
  | MallocLet { memArgs; body } ->
    let memArgsOld = memArgs in
    let memArgs =
      List.filter memArgs ~f:(fun { memBinding; memType = _; memLoc = _ } ->
        Set.mem uses memBinding)
    in
    if not (List.length memArgs = List.length memArgsOld)
    then
      Stdio.prerr_endline
        (Printf.sprintf
           "old: %s\nnew: %s"
           (Sexp.to_string_hum
              ([%sexp_of: Identifier.t list]
                 (List.map memArgsOld ~f:(fun { memBinding; memType = _; memLoc = _ } ->
                    memBinding))))
           (Sexp.to_string_hum
              ([%sexp_of: Identifier.t list]
                 (List.map memArgs ~f:(fun { memBinding; memType = _; memLoc = _ } ->
                    memBinding)))));
    let body = rewriteWithoutUnusedVars body uses in
    MallocLet { memArgs; body }
  | ReifyDimensionIndex d -> ReifyDimensionIndex d
  | ShapeProd p -> ShapeProd p
  | LoopBlock lb ->
    let lb = rewriteWithoutUnusedVarsLoopBlock lb uses in
    LoopBlock lb
  | LoopKernel
      { kernel = { mapResultMemDeviceInterim; loopBlock }; captures; blocks; threads } ->
    let loopBlock = rewriteWithoutUnusedVarsLoopBlock loopBlock uses in
    let kernel = { mapResultMemDeviceInterim; loopBlock } in
    LoopKernel { kernel; captures; blocks; threads }
  | Let { args; body } ->
    let argsOld = args in
    let args = List.filter args ~f:(fun { binding; value = _ } -> Set.mem uses binding) in
    if not (List.length args = List.length argsOld)
    then
      Stdio.prerr_endline
        (Printf.sprintf
           "old: %s\nnew: %s"
           (Sexp.to_string_hum
              ([%sexp_of: Identifier.t list]
                 (List.map argsOld ~f:(fun { binding; value = _ } -> binding))))
           (Sexp.to_string_hum
              ([%sexp_of: Identifier.t list]
                 (List.map args ~f:(fun { binding; value = _ } -> binding)))));
    let body = rewriteWithoutUnusedVars body uses in
    Let { args; body }
  | Box { indices; body; type' } ->
    let body = rewriteWithoutUnusedVars body uses in
    Box { indices; body; type' }
  | Literal l -> Literal l
  | Values { elements; type' } ->
    let elements = List.map elements ~f:(fun e -> rewriteWithoutUnusedVars e uses) in
    Values { elements; type' }
  | ScalarPrimitive { op; args; type' } ->
    let args = List.map args ~f:(fun a -> rewriteWithoutUnusedVars a uses) in
    ScalarPrimitive { op; args; type' }
  | TupleDeref { index; tuple; type' } ->
    let tuple = rewriteWithoutUnusedVars tuple uses in
    TupleDeref { index; tuple; type' }
  | ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' } ->
    let arrayArg = rewriteWithoutUnusedVars arrayArg uses in
    let indexArg = rewriteWithoutUnusedVars indexArg uses in
    ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' }
  | IfParallelismHitsCutoff { parallelism; cutoff; then'; else'; type' } ->
    let then' = rewriteWithoutUnusedVars then' uses in
    let else' = rewriteWithoutUnusedVars else' uses in
    IfParallelismHitsCutoff { parallelism; cutoff; then'; else'; type' }
  | Eseq { statement; expr; type' } ->
    let statement = rewriteWithoutUnusedVarsStatement statement uses in
    let expr = rewriteWithoutUnusedVars expr uses in
    Eseq { statement; expr; type' }
  | Getmem m -> Getmem m

and rewriteWithoutUnusedVarsStatement
  : type l.
    (l, captures) Acorn.Expr.statement
    -> (Identifier.t, _) Set.t
    -> (l, captures) Acorn.Expr.statement
  =
  fun stmt uses ->
  match stmt with
  | Putmem { expr; addr; type' } ->
    let expr = rewriteWithoutUnusedVars expr uses in
    Putmem { expr; addr; type' }
  | MapKernel
      { kernel = { label; map; mapResultMemDeviceInterim; mapResultMemHostFinal }
      ; captures
      ; blocks
      ; threads
      } ->
    let map = rewriteWithoutUnusedVarsMapInKernel map uses in
    let kernel = { label; map; mapResultMemDeviceInterim; mapResultMemHostFinal } in
    MapKernel { kernel; captures; blocks; threads }
  | ComputeForSideEffects expr ->
    let expr = rewriteWithoutUnusedVars expr uses in
    ComputeForSideEffects expr
  | Statements stmts ->
    let stmts = List.map stmts ~f:(fun s -> rewriteWithoutUnusedVarsStatement s uses) in
    Statements stmts
  | SLet { args; body } ->
    let args = List.filter args ~f:(fun { binding; value = _ } -> Set.mem uses binding) in
    let body = rewriteWithoutUnusedVarsStatement body uses in
    SLet { args; body }
  | SMallocLet { memArgs; body } ->
    let memArgs =
      List.filter memArgs ~f:(fun { memBinding; memType = _; memLoc = _ } ->
        Set.mem uses memBinding)
    in
    let body = rewriteWithoutUnusedVarsStatement body uses in
    SMallocLet { memArgs; body }
  | ReifyShapeIndex i -> ReifyShapeIndex i

and rewriteWithoutUnusedVarsMapInKernel
  { frameShape; indexMode; mapArgs; mapMemArgs; mapIotas; mapBody; type' }
  uses
  =
  let mapBody = rewriteWithoutUnusedVarsMapBody mapBody uses in
  { frameShape; indexMode; mapArgs; mapMemArgs; mapIotas; mapBody; type' }

and rewriteWithoutUnusedVarsMapBody body uses =
  match body with
  | MapBodyStatement stmt ->
    let stmt = rewriteWithoutUnusedVarsStatement stmt uses in
    MapBodyStatement stmt
  | MapBodySubMaps maps ->
    let maps = List.map maps ~f:(fun m -> rewriteWithoutUnusedVarsMapInKernel m uses) in
    MapBodySubMaps maps

and rewriteWithoutUnusedVarsConsumer
  : type o i p.
    (o, i, p, _) consumerOp -> (Identifier.t, _) Set.t -> (o, i, p, _) consumerOp
  =
  fun consumer uses ->
  match consumer with
  | ReduceSeq { arg; zero; body; indexMode; d; type' } ->
    let zero = rewriteWithoutUnusedVars zero uses in
    let body = rewriteWithoutUnusedVars body uses in
    ReduceSeq { arg; zero; body; indexMode; d; type' }
  | ReducePar
      { reduce = { arg; zero; body; indexMode; d; type' }
      ; interimResultMemDeviceInterim
      ; interimResultMemHostFinal
      ; outerBody
      } ->
    let zero = rewriteWithoutUnusedVars zero uses in
    let body = rewriteWithoutUnusedVars body uses in
    let outerBody = rewriteWithoutUnusedVars outerBody uses in
    let reduce = { arg; zero; body; indexMode; d; type' } in
    ReducePar
      { reduce; interimResultMemHostFinal; interimResultMemDeviceInterim; outerBody }
  | ScanSeq { arg; zero; body; indexMode; d; scanResultMemFinal; type' } ->
    let zero = rewriteWithoutUnusedVars zero uses in
    let body = rewriteWithoutUnusedVars body uses in
    ScanSeq { arg; zero; body; indexMode; d; scanResultMemFinal; type' }
  | ScanPar
      { scan = { arg; zero; body; indexMode; d; scanResultMemFinal; type' }
      ; scanResultMemDeviceInterim
      } ->
    let zero = rewriteWithoutUnusedVars zero uses in
    let body = rewriteWithoutUnusedVars body uses in
    let scan = { arg; zero; body; indexMode; d; scanResultMemFinal; type' } in
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
    let zeroValue = rewriteWithoutUnusedVars zeroValue uses in
    let zeroArg = { zeroBinding; zeroValue } in
    let body = rewriteWithoutUnusedVars body uses in
    Fold { zeroArg; arrayArgs; mappedMemArgs; reverse; body; d; character; type' }

and rewriteWithoutUnusedVarsLoopBlock
  : type o i p e.
    (o, i, p, captures, e) loopBlock
    -> (Identifier.t, _) Set.t
    -> (o, i, p, captures, e) loopBlock
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
      uses ->
  let mapBody = rewriteWithoutUnusedVars mapBody uses in
  let consumer =
    Maybe.map consumer ~f:(fun c -> rewriteWithoutUnusedVarsConsumer c uses)
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
;;

let deleteUnusedVars
  : type l. (l, Acorn.Expr.captures) Acorn.Expr.t -> (l, Acorn.Expr.captures) Acorn.Expr.t
  =
  fun expr ->
  let uses = findUses expr in
  Stdio.prerr_endline
    (Printf.sprintf
       "Uses: \n%s"
       (Sexp.to_string_hum ([%sexp_of: Identifier.t list] (Set.to_list uses))));
  let expr = rewriteWithoutUnusedVars expr uses in
  expr
;;

let simplify expr =
  let open State in
  let expr = deleteUnusedVars expr in
  return expr
;;

module Stage (SB : Source.BuilderT) = struct
  type state = CompilerState.state
  type input = Acorn.withCaptures
  type output = Acorn.withCaptures
  type error = (SB.source option, string) Source.annotate

  let name = "Simplify AST"

  let run input =
    CompilerPipeline.S.make ~f:(fun inputState -> State.run (simplify input) inputState)
  ;;
end
