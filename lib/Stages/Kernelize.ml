open! Base
module Index = Corn.Index
module Type = Corn.Type

type host = Corn.Expr.host [@@deriving sexp_of]
type device = Corn.Expr.device [@@deriving sexp_of]

(* module KernelizeState = struct *)
(*   include State *)

(*   type state = CompilerState.state *)
(*   type ('a, 'e) u = (state, 'a, 'e) t *)

(*   let getDeviceInfo () = get () >>| fun (s : state) -> s.deviceInfo *)

(*   let createId name = *)
(*     make ~f:(fun state -> *)
(*       State.run *)
(*         (Identifier.create *)
(*            name *)
(*            ~getCounter:(fun (s : state) -> s.idCounter) *)
(*            ~setCounter:(fun (s : state) idCounter -> { s with idCounter })) *)
(*         state) *)
(*   ;; *)
(* end *)

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

(* let getThreads *)
(*   (_ : DeviceInfo.t) *)
(*   (consumer : (host, device, Corn.Expr.parallel) Corn.Expr.consumerOp option) *)
(*   = *)
(*   match consumer with *)
(*   | None | Some (Scatter _) -> 256 *)
(*   | Some (ReducePar _) -> 32 *)
(*   | Some (ScanPar _) -> 256 *)
(* ;; *)

(* let getBlocks ~threads:threadsPerBlock ~parShape deviceInfo = *)
(*   let blocksToReachThreads threads = (threads + threadsPerBlock - 1) / threadsPerBlock in *)
(*   let maxBlocks = blocksToReachThreads (DeviceInfo.maxThreads deviceInfo) in *)
(*   match ParallelismShape.known parShape with *)
(*   | Some parShape -> Int.min (blocksToReachThreads parShape) maxBlocks *)
(*   | None -> maxBlocks *)
(* ;; *)

(* let decideParallelism ~par:(parExpr, parParShape) ~seq:(seqExpr, seqParShape) = *)
(*   let open KernelizeState.Let_syntax in *)
(*   let%map deviceInfo = KernelizeState.getDeviceInfo () in *)
(*   let type' = Corn.Expr.type' parExpr in *)
(*   match *)
(*     ( ParallelismWorthwhileness.get deviceInfo parParShape *)
(*     , ParallelismWorthwhileness.get deviceInfo seqParShape ) *)
(*   with *)
(*   | Saturating, _ *)
(*   | Worthwhile { bound = _ }, NotWorthwhile { bound = Some _ } *)
(*   | Worthwhile { bound = Some _ }, NotWorthwhile { bound = None } -> parExpr, parParShape *)
(*   | NotWorthwhile { bound = Some _ }, _ | _, Saturating -> seqExpr, seqParShape *)
(*   | Worthwhile { bound = Some parBound }, Worthwhile { bound = Some seqBound } -> *)
(*     if parBound >= seqBound then parExpr, parParShape else seqExpr, seqParShape *)
(*   | NotWorthwhile { bound = None }, NotWorthwhile { bound = Some _ } -> *)
(*     ( Corn.Expr.IfParallelismHitsCutoff *)
(*         { parallelism = ParallelismShape.toCorn parParShape *)
(*         ; cutoff = ParallelismWorthwhileness.worthwhileParallelismCutoff deviceInfo *)
(*         ; then' = parExpr *)
(*         ; else' = seqExpr *)
(*         ; type' *)
(*         } *)
(*     , parParShape ) *)
(*   | Worthwhile { bound = Some parBound }, Worthwhile { bound = None } -> *)
(*     if parBound >= ParallelismShape.parallelismFloor seqParShape *)
(*     then parExpr, parParShape *)
(*     else seqExpr, seqParShape *)
(*   | ( (Worthwhile { bound = None } | NotWorthwhile { bound = None }) *)
(*     , (Worthwhile { bound = _ } | NotWorthwhile { bound = None }) ) -> *)
(*     ( Corn.Expr.IfParallelismHitsCutoff *)
(*         { parallelism = ParallelismShape.toCorn parParShape *)
(*         ; cutoff = ParallelismShape.parallelismFloor seqParShape *)
(*         ; then' = parExpr *)
(*         ; else' = seqExpr *)
(*         ; type' *)
(*         } *)
(*     , ParallelismShape.max [ parParShape; seqParShape ] ) *)
(* ;; *)

(* let rec getOpts (expr : Nested.t) : (compilationOptions, _) KernelizeState.u = *)
(*   let open KernelizeState.Let_syntax in *)
(*   let open Corn in *)
(*   match expr with *)
(*   | Ref ref -> *)
(*     return *)
(*     @@ compilationOptions *)
(*          ~hostExpr:(Ref ref) *)
(*          ~deviceExpr:(Ref ref) *)
(*          ~hostParShape:(Known 1) *)
(*   | Frame { elements; dimension; type' } -> *)
(*     let%map hostElements, deviceElements, hostParShape, _, _ = getOptsList elements in *)
(*     compilationOptions *)
(*       ~hostExpr:(Frame { elements = hostElements; dimension; type' }) *)
(*       ~deviceExpr:(Frame { elements = deviceElements; dimension; type' }) *)
(*       ~hostParShape *)
(*   | BoxValue { box; type' } -> *)
(*     let%map boxOpts = getOpts box in *)
(*     compilationOptions *)
(*       ~hostExpr:(BoxValue { box = boxOpts.hostExpr; type' }) *)
(*       ~deviceExpr:(BoxValue { box = boxOpts.deviceExpr; type' }) *)
(*       ~hostParShape:boxOpts.hostParShape *)
(*   | IndexLet { indexArgs; body; type' } -> *)
(*     let%map indexArgsHostExprs, indexArgsDeviceExprs, indexArgsHostParShapes = *)
(*       indexArgs *)
(*       |> List.map ~f:(fun { indexBinding; indexValue; sort } -> *)
(*         let%map indexValueHostExpr, indexValueDeviceExpr, indexValueHostParShape = *)
(*           match indexValue with *)
(*           | Runtime value -> *)
(*             let%map valueOpts = getOpts value in *)
(*             ( Expr.Runtime valueOpts.hostExpr *)
(*             , Expr.Runtime valueOpts.deviceExpr *)
(*             , valueOpts.hostParShape ) *)
(*           | FromBox { box; i } -> *)
(*             let%map boxOpts = getOpts box in *)
(*             ( Expr.FromBox { box = boxOpts.hostExpr; i } *)
(*             , Expr.FromBox { box = boxOpts.deviceExpr; i } *)
(*             , boxOpts.hostParShape ) *)
(*         in *)
(*         ( Expr.{ indexBinding; indexValue = indexValueHostExpr; sort } *)
(*         , Expr.{ indexBinding; indexValue = indexValueDeviceExpr; sort } *)
(*         , indexValueHostParShape )) *)
(*       |> KernelizeState.all *)
(*       >>| List.unzip3 *)
(*     and bodyOpts = getOpts body in *)
(*     let indexArgsHostParShape = ParallelismShape.max indexArgsHostParShapes in *)
(*     compilationOptions *)
(*       ~hostExpr: *)
(*         (IndexLet { indexArgs = indexArgsHostExprs; body = bodyOpts.hostExpr; type' }) *)
(*       ~deviceExpr: *)
(*         (IndexLet { indexArgs = indexArgsDeviceExprs; body = bodyOpts.deviceExpr; type' }) *)
(*       ~hostParShape: *)
(*         (ParallelismShape.max [ indexArgsHostParShape; bodyOpts.hostParShape ]) *)
(*   | ReifyIndex reifyIndex -> *)
(*     return *)
(*     @@ compilationOptions *)
(*          ~hostExpr:(ReifyIndex reifyIndex) *)
(*          ~deviceExpr:(ReifyIndex reifyIndex) *)
(*          ~hostParShape:ParallelismShape.empty *)
(*   | ShapeProd shape -> *)
(*     return *)
(*     @@ compilationOptions *)
(*          ~hostExpr:(ShapeProd shape) *)
(*          ~deviceExpr:(ShapeProd shape) *)
(*          ~hostParShape:ParallelismShape.empty *)
(*   | Let { args; body; type' } -> *)
(*     let%map argsHost, argsDevice, argsHostParShapes = *)
(*       args *)
(*       |> List.map ~f:(fun { binding; value } -> *)
(*         let%map valueOpts = getOpts value in *)
(*         ( Expr.{ binding; value = valueOpts.hostExpr } *)
(*         , Expr.{ binding; value = valueOpts.deviceExpr } *)
(*         , valueOpts.hostParShape )) *)
(*       |> KernelizeState.all *)
(*       >>| List.unzip3 *)
(*     and bodyOpts = getOpts body in *)
(*     let argsHostParShape = ParallelismShape.max argsHostParShapes in *)
(*     compilationOptions *)
(*       ~hostExpr:(Let { args = argsHost; body = bodyOpts.hostExpr; type' }) *)
(*       ~deviceExpr:(Let { args = argsDevice; body = bodyOpts.deviceExpr; type' }) *)
(*       ~hostParShape:(ParallelismShape.max [ argsHostParShape; bodyOpts.hostParShape ]) *)
(*   | LoopBlock *)
(*       { frameShape *)
(*       ; label = _ *)
(*       ; mapArgs *)
(*       ; mapIotas *)
(*       ; mapBody *)
(*       ; mapBodyMatcher *)
(*       ; mapResults *)
(*       ; consumer = None *)
(*       ; type' *)
(*       } -> *)
(*     let%bind mapBodyOpts = getOpts mapBody in *)
(*     let mapAsKernel : Expr.mapKernel = *)
(*       { frameShape *)
(*       ; mapArgs *)
(*       ; mapIotas *)
(*       ; mapBody = mapBodyOpts.flattenedMapBody *)
(*       ; mapBodyMatcher *)
(*       ; mapResults *)
(*       ; type' = List.nth_exn type' 0 *)
(*       } *)
(*     in *)
(*     let mapAsKernelParShape = *)
(*       ParallelismShape.nestParallelism frameShape mapBodyOpts.flattenedMapBodyParShape *)
(*     in *)
(*     let mapAsHostExpr = *)
(*       Expr.LoopBlock *)
(*         { frameShape *)
(*         ; mapArgs *)
(*         ; mapIotas *)
(*         ; mapBody = mapBodyOpts.hostExpr *)
(*         ; mapBodyMatcher *)
(*         ; mapResults *)
(*         ; consumer = Nothing *)
(*         ; indexMode = None *)
(*         ; type' *)
(*         } *)
(*     in *)
(*     (\* let%bind deviceInfo = KernelizeState.getDeviceInfo () in *)
(*        let threads = getThreads deviceInfo None in *)
(*        let blocks = getBlocks ~threads ~parShape:mapAsKernelParShape deviceInfo in *\) *)
(*     let%map hostExpr, hostParShape = *)
(*       decideParallelism *)
(*         ~par:(mapAsHostExpr, mapBodyOpts.hostParShape) *)
(*           (\* ( Expr.values *)
(*              [ Expr.MapKernel { kernel = mapAsKernel; blocks; threads }; Expr.values [] ] *)
(*              , mapAsKernelParShape ) *\) *)
(*         ~seq:(mapAsHostExpr, mapBodyOpts.hostParShape) *)
(*     in *)
(*     { hostExpr *)
(*     ; deviceExpr = *)
(*         LoopBlock *)
(*           { frameShape *)
(*           ; mapArgs *)
(*           ; mapIotas *)
(*           ; mapBody = mapBodyOpts.deviceExpr *)
(*           ; mapBodyMatcher *)
(*           ; mapResults *)
(*           ; consumer = Nothing *)
(*           ; indexMode = None *)
(*           ; type' *)
(*           } *)
(*     ; hostParShape *)
(*     ; flattenedMapBody = *)
(*         MapBodySubMap (MapBodyValues [ MapBodyMap mapAsKernel; MapBodyValues [] ]) *)
(*     ; flattenedMapBodyParShape = mapAsKernelParShape *)
(*     } *)
(*   | LoopBlock *)
(*       { frameShape *)
(*       ; mapArgs *)
(*       ; mapIotas *)
(*       ; mapBody *)
(*       ; mapBodyMatcher *)
(*       ; mapResults *)
(*       ; consumer = Some consumer *)
(*       ; label = _ *)
(*       ; type' *)
(*       } -> *)
(*     let%bind consumerAsHostExpr, consumerAsDeviceExpr, consumerAsHostParShape, parConsumer *)
(*       = *)
(*       match consumer with *)
(*       | Reduce { arg; zero; body; d; character; type' } -> *)
(*         let makeSeq ~(character : Nested.Expr.reduceCharacter) reduceLike = *)
(*           match character with *)
(*           | Reduce -> Expr.ReduceSeq reduceLike *)
(*           | Scan -> Expr.ScanSeq reduceLike *)
(*         in *)
(*         let makePar ~(character : Nested.Expr.reduceCharacter) ~outerBody reduceLike = *)
(*           match character with *)
(*           | Reduce -> Expr.ReducePar { reduce = reduceLike; outerBody } *)
(*           | Scan -> Expr.ScanPar reduceLike *)
(*         in *)
(*         let%map zeroOpts = getOpts zero *)
(*         and bodyOpts = getOpts body in *)
(*         let zeroOptsHostParShape = hostParShape zeroOpts in *)
(*         ( makeSeq *)
(*             ~character *)
(*             { arg; zero = hostExpr zeroOpts; body = bodyOpts.hostExpr; d; type' } *)
(*         , makeSeq *)
(*             ~character *)
(*             { arg; zero = deviceExpr zeroOpts; body = bodyOpts.deviceExpr; d; type' } *)
(*         , ParallelismShape.max [ bodyOpts.hostParShape; zeroOptsHostParShape ] *)
(*         , Some *)
(*             ( makePar *)
(*                 ~character *)
(*                 ~outerBody:bodyOpts.hostExpr *)
(*                 { arg; zero = hostExpr zeroOpts; body = bodyOpts.deviceExpr; d; type' } *)
(*             , ParallelismShape.max *)
(*                 [ ParallelismShape.singleDimensionParallelism (Add d) *)
(*                 ; zeroOptsHostParShape *)
(*                 ] ) ) *)
(*       | Fold { zeroArg; arrayArgs; body; reverse; d; character; type' } -> *)
(*         let%map bodyOpts = getOpts body *)
(*         and zeroArgValueOpts = getOpts zeroArg.zeroValue in *)
(*         ( Expr.Fold *)
(*             { zeroArg = *)
(*                 { zeroBinding = zeroArg.zeroBinding *)
(*                 ; zeroValue = zeroArgValueOpts.hostExpr *)
(*                 } *)
(*             ; arrayArgs *)
(*             ; body = bodyOpts.hostExpr *)
(*             ; reverse *)
(*             ; d *)
(*             ; character *)
(*             ; type' *)
(*             } *)
(*         , Expr.Fold *)
(*             { zeroArg = *)
(*                 { zeroBinding = zeroArg.zeroBinding *)
(*                 ; zeroValue = zeroArgValueOpts.deviceExpr *)
(*                 } *)
(*             ; arrayArgs *)
(*             ; body = bodyOpts.deviceExpr *)
(*             ; reverse *)
(*             ; d *)
(*             ; character *)
(*             ; type' *)
(*             } *)
(*         , ParallelismShape.max [ bodyOpts.hostParShape; zeroArgValueOpts.hostParShape ] *)
(*         , None ) *)
(*       | Scatter { valuesArg; indicesArg; dIn; dOut; type' } -> *)
(*         let scatter = Expr.Scatter { valuesArg; indicesArg; dIn; dOut; type' } in *)
(*         return *)
(*           ( scatter *)
(*           , scatter *)
(*           , ParallelismShape.empty *)
(*           , Some (scatter, ParallelismShape.singleDimensionParallelism (Add dIn)) ) *)
(*     and mapBodyOpts = getOpts mapBody in *)
(*     let sequentialBlockParShape = *)
(*       ParallelismShape.max [ mapBodyOpts.hostParShape; consumerAsHostParShape ] *)
(*     in *)
(*     let%map hostExpr, hostParShape = *)
(*       match parConsumer with *)
(*       | Some _ -> *)
(*         (\* | Some (parConsumerExpr, parConsumerParShape) -> *\) *)
(*         let%bind _ = KernelizeState.getDeviceInfo () in *)
(*         (\* let threads = getThreads deviceInfo (Some parConsumerExpr) in *\) *)
(*         (\* let blocks = getBlocks ~threads ~parShape:parConsumerParShape deviceInfo in *\) *)
(*         decideParallelism *)
(*           ~par: *)
(*             ( Expr.LoopBlock *)
(*                 { frameShape *)
(*                 ; mapArgs *)
(*                 ; mapIotas *)
(*                 ; mapBody = mapBodyOpts.hostExpr *)
(*                 ; mapBodyMatcher *)
(*                 ; mapResults *)
(*                 ; consumer = Just consumerAsHostExpr *)
(*                 ; indexMode = None *)
(*                 ; type' *)
(*                 } *)
(*             , sequentialBlockParShape ) *)
(*             (\* ( Expr.LoopKernel *)
(*                 { kernel = *)
(*                     { frameShape *)
(*                     ; mapArgs *)
(*                     ; mapIotas *)
(*                     ; mapBody = mapBodyOpts.deviceExpr *)
(*                     ; mapBodyMatcher *)
(*                     ; mapResults *)
(*                     ; consumer = Just parConsumerExpr *)
(*                     ; type' *)
(*                     } *)
(*                 ; blocks *)
(*                 ; threads *)
(*                 } *)
(*             , parConsumerParShape ) *\) *)
(*           ~seq: *)
(*             ( Expr.LoopBlock *)
(*                 { frameShape *)
(*                 ; mapArgs *)
(*                 ; mapIotas *)
(*                 ; mapBody = mapBodyOpts.hostExpr *)
(*                 ; mapBodyMatcher *)
(*                 ; mapResults *)
(*                 ; consumer = Just consumerAsHostExpr *)
(*                 ; indexMode = None *)
(*                 ; type' *)
(*                 } *)
(*             , sequentialBlockParShape ) *)
(*       | None -> *)
(*         (\* TODO: might be a good idea to unfuse and parallelize just the map *\) *)
(*         return *)
(*           ( Expr.LoopBlock *)
(*               { frameShape *)
(*               ; mapArgs *)
(*               ; mapIotas *)
(*               ; mapBody = mapBodyOpts.hostExpr *)
(*               ; mapBodyMatcher *)
(*               ; mapResults *)
(*               ; consumer = Just consumerAsHostExpr *)
(*               ; indexMode = None *)
(*               ; type' *)
(*               } *)
(*           , sequentialBlockParShape ) *)
(*     in *)
(*     let opts = *)
(*       compilationOptions *)
(*         ~hostExpr *)
(*         ~deviceExpr: *)
(*           (LoopBlock *)
(*              { frameShape *)
(*              ; mapArgs *)
(*              ; mapIotas *)
(*              ; mapBody = mapBodyOpts.deviceExpr *)
(*              ; mapBodyMatcher *)
(*              ; mapResults *)
(*              ; consumer = Just consumerAsDeviceExpr *)
(*              ; indexMode = None *)
(*              ; type' *)
(*              }) *)
(*         ~hostParShape *)
(*     in *)
(*     opts *)
(*   | Box { indices; body; bodyType; type' } -> *)
(*     let%map bodyOpts = getOpts body in *)
(*     compilationOptions *)
(*       ~hostExpr:(Box { indices; body = bodyOpts.hostExpr; bodyType; type' }) *)
(*       ~deviceExpr:(Box { indices; body = bodyOpts.deviceExpr; bodyType; type' }) *)
(*       ~hostParShape:bodyOpts.hostParShape *)
(*   | Literal literal -> *)
(*     return *)
(*     @@ compilationOptions *)
(*          ~hostExpr:(Literal literal) *)
(*          ~deviceExpr:(Literal literal) *)
(*          ~hostParShape:ParallelismShape.empty *)
(*   | Values { elements; type' } -> *)
(*     let%map ( elementsHostExprs *)
(*             , elementsDeviceExprs *)
(*             , elementsHostParShape *)
(*             , elementsFlattenedMapBodies *)
(*             , elementsFlattenedMapBodiesParShape ) *)
(*       = *)
(*       getOptsList elements *)
(*     in *)
(*     let deviceExpr = Expr.Values { elements = elementsDeviceExprs; type' } in *)
(*     let list_all_opt l = *)
(*       let filtered = List.filter_opt l in *)
(*       if List.length l = List.length filtered then Some filtered else None *)
(*     in *)
(*     let elementsFlattenedMapBodiesAsSubMaps = *)
(*       elementsFlattenedMapBodies *)
(*       |> List.map ~f:(function *)
(*         | Expr.MapBodyExpr _ -> None *)
(*         | Expr.MapBodySubMap subMap -> Some subMap) *)
(*       |> list_all_opt *)
(*     in *)
(*     let flattenedMapBody, flattenedMapBodyParShape = *)
(*       match elementsFlattenedMapBodiesAsSubMaps with *)
(*       | Some elementsFlattenedMapBodies -> *)
(*         ( Expr.MapBodySubMap (MapBodyValues elementsFlattenedMapBodies) *)
(*         , elementsFlattenedMapBodiesParShape ) *)
(*       | None -> Expr.MapBodyExpr deviceExpr, ParallelismShape.empty *)
(*     in *)
(*     { hostExpr = Values { elements = elementsHostExprs; type' } *)
(*     ; deviceExpr *)
(*     ; hostParShape = elementsHostParShape *)
(*     ; flattenedMapBody *)
(*     ; flattenedMapBodyParShape *)
(*     } *)
(*   | ScalarPrimitive { op; args; type' } -> *)
(*     let%map argsHostExprs, argsDeviceExprs, argsHostParShape, _, _ = getOptsList args in *)
(*     compilationOptions *)
(*       ~hostExpr:(ScalarPrimitive { op; args = argsHostExprs; type' }) *)
(*       ~deviceExpr:(ScalarPrimitive { op; args = argsDeviceExprs; type' }) *)
(*       ~hostParShape:argsHostParShape *)
(*   | TupleDeref { tuple; index; type' } -> *)
(*     let%map tupleOpts = getOpts tuple in *)
(*     let hostExpr = *)
(*       match tupleOpts.hostExpr with *)
(*       | Values { elements; type' = _ } -> List.nth_exn elements index *)
(*       | tuple -> TupleDeref { tuple; index; type' } *)
(*     in *)
(*     let deviceExpr = *)
(*       match tupleOpts.deviceExpr with *)
(*       | Values { elements; type' = _ } -> List.nth_exn elements index *)
(*       | tuple -> TupleDeref { tuple; index; type' } *)
(*     in *)
(*     let flattenedMapBody, flattenedMapBodyParShape = *)
(*       match tupleOpts.flattenedMapBody with *)
(*       | MapBodyExpr _ -> Expr.MapBodyExpr deviceExpr, ParallelismShape.empty *)
(*       | MapBodySubMap (MapBodyValues values) -> *)
(*         Expr.MapBodySubMap (List.nth_exn values index), tupleOpts.flattenedMapBodyParShape *)
(*       | MapBodySubMap subMaps -> *)
(*         ( Expr.MapBodySubMap (MapBodyDeref { tuple = subMaps; index }) *)
(*         , tupleOpts.flattenedMapBodyParShape ) *)
(*     in *)
(*     { hostExpr *)
(*     ; deviceExpr *)
(*     ; hostParShape = tupleOpts.hostParShape *)
(*     ; flattenedMapBody *)
(*     ; flattenedMapBodyParShape *)
(*     } *)
(*   | ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' } -> *)
(*     let%map arrayArgOpts = getOpts arrayArg *)
(*     and indexArgOpts = getOpts indexArg in *)
(*     compilationOptions *)
(*       ~hostExpr: *)
(*         (ContiguousSubArray *)
(*            { arrayArg = arrayArgOpts.hostExpr *)
(*            ; indexArg = indexArgOpts.hostExpr *)
(*            ; originalShape *)
(*            ; resultShape *)
(*            ; type' *)
(*            }) *)
(*       ~deviceExpr: *)
(*         (ContiguousSubArray *)
(*            { arrayArg = arrayArgOpts.deviceExpr *)
(*            ; indexArg = indexArgOpts.deviceExpr *)
(*            ; originalShape *)
(*            ; resultShape *)
(*            ; type' *)
(*            }) *)
(*       ~hostParShape: *)
(*         (ParallelismShape.max [ arrayArgOpts.hostParShape; indexArgOpts.hostParShape ]) *)
(*   | Append { args; type' } -> *)
(*     let%map argsHostExprs, argsDeviceExprs, argsHostParShape, _, _ = getOptsList args in *)
(*     compilationOptions *)
(*       ~hostExpr:(Append { args = argsHostExprs; type' }) *)
(*       ~deviceExpr:(Append { args = argsDeviceExprs; type' }) *)
(*       ~hostParShape:argsHostParShape *)
(*   | Zip { zipArg; nestCount; type' } -> *)
(*     let%map zipArgOpts = getOpts zipArg in *)
(*     compilationOptions *)
(*       ~hostExpr:(Zip { zipArg = zipArgOpts.hostExpr; nestCount; type' }) *)
(*       ~deviceExpr:(Zip { zipArg = zipArgOpts.deviceExpr; nestCount; type' }) *)
(*       ~hostParShape:zipArgOpts.hostParShape *)
(*   | Unzip { unzipArg; type' } -> *)
(*     let%map unzipArgOpts = getOpts unzipArg in *)
(*     compilationOptions *)
(*       ~hostExpr:(Unzip { unzipArg = unzipArgOpts.hostExpr; type' }) *)
(*       ~deviceExpr:(Unzip { unzipArg = unzipArgOpts.deviceExpr; type' }) *)
(*       ~hostParShape:unzipArgOpts.hostParShape *)

(* and getOptsList exprs = *)
(*   let open KernelizeState.Let_syntax in *)
(*   let%map optss = exprs |> List.map ~f:getOpts |> KernelizeState.all in *)
(*   let hostExprs = List.map optss ~f:hostExpr in *)
(*   let deviceExprs = List.map optss ~f:deviceExpr in *)
(*   let hostParShapes = List.map optss ~f:hostParShape in *)
(*   let flattenedMapBodies = List.map optss ~f:(fun o -> o.flattenedMapBody) in *)
(*   let flattenedMapBodiesParShape = *)
(*     List.map optss ~f:(fun o -> o.flattenedMapBodyParShape) *)
(*   in *)
(*   ( hostExprs *)
(*   , deviceExprs *)
(*   , ParallelismShape.max hostParShapes *)
(*   , flattenedMapBodies *)
(*   , ParallelismShape.max flattenedMapBodiesParShape ) *)
(* ;; *)

type loopStructureTree =
  | Leaf
  (* needs multiple children like frame or values but not an actual loop *)
  | Split : { children : loopStructureTree list } -> loopStructureTree
  | LoopNode :
      { children : loopStructureTree list
      ; frameShape : Index.shapeElement
      }
      -> loopStructureTree
[@@deriving sexp_of]

let split children : loopStructureTree =
  match children with
  | [] -> Leaf
  | [ node ] -> node
  | _ -> Split { children }
;;

let rec extractLoopStructure (expr : Nested.t) : loopStructureTree =
  match expr with
  | Literal _ -> Leaf
  | ScalarPrimitive _ -> Leaf
  | Ref _ -> Leaf
  | Frame { elements; dimension = _; type' = _ } ->
    let children = extractLoopStructureList elements in
    split children
  | BoxValue bv -> extractLoopStructure bv.box
  | IndexLet { indexArgs; body; type' = _ } ->
    let tArgs =
      List.map
        ~f:(fun { indexValue; indexBinding = _; sort = _ } ->
          match indexValue with
          | Runtime t -> t
          | FromBox { box; i = _ } -> box)
        indexArgs
    in
    let children = extractLoopStructureList (body :: tArgs) in
    split children
  | ReifyIndex _ -> Leaf
  | ShapeProd _ -> Leaf
  | Let { args; body; type' = _ } ->
    let args = List.map ~f:(fun { binding = _; value } -> value) args in
    let children = extractLoopStructureList (body :: args) in
    split children
  | LoopBlock lb ->
    let mapBodyChild = extractLoopStructure lb.mapBody in
    let consumerChild = extractLoopStructureConsumerHelper lb.consumer in
    let children =
      List.filter
        ~f:(fun c ->
          match c with
          | Leaf -> false
          | Split _ -> true
          | LoopNode _ -> true)
        [ mapBodyChild; consumerChild ]
    in
    LoopNode { children; frameShape = lb.frameShape }
  | Box b -> extractLoopStructure b.body
  | Values { elements; type' = _ } ->
    let children = extractLoopStructureList elements in
    split children
  | TupleDeref { tuple; index = _; type' = _ } -> extractLoopStructure tuple
  | ContiguousSubArray
      { arrayArg; indexArg; originalShape = _; resultShape = _; type' = _ } ->
    let children = extractLoopStructureList [ arrayArg; indexArg ] in
    split children
  | Append { args; type' = _ } ->
    let children = extractLoopStructureList args in
    Split { children }
  | Zip { zipArg; nestCount = _; type' = _ } -> extractLoopStructure zipArg
  | Unzip { unzipArg; type' = _ } -> extractLoopStructure unzipArg

and extractLoopStructureConsumerHelper (consumer : Nested.Expr.consumerOp option)
  : loopStructureTree
  =
  let open Nested.Expr in
  match consumer with
  | None -> Leaf
  | Some consumer ->
    (match consumer with
     | Reduce { zero; body; arg = _; d = _; character = _; type' = _ } ->
       split (extractLoopStructureList [ zero; body ])
     | Fold { zeroArg; arrayArgs = _; body; reverse = _; d = _; character = _; type' = _ }
       -> split (extractLoopStructureList [ zeroArg.zeroValue; body ])
     | Scatter { valuesArg = _; indicesArg = _; dIn = _; dOut = _; type' = _ } -> Leaf)

and extractLoopStructureList (elements : Nested.t list) : loopStructureTree list =
  List.filter_map elements ~f:(fun e ->
    match extractLoopStructure e with
    | Leaf -> None
    | rest -> Some rest)
;;

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

(* TODO: maybe worth it to also count how many seq instructions are done in different parallel modes, maybe
   (* sometimes it's worth it to have multiple kernels vs a single larger one *)
let rec tryToParallelize (expr : Nested.t) (structureMap : IndexingModeDrafting.cuda_t)
  : Nested.t * IndexingModeDrafting.cuda_t * IndexingModeDrafting.index_cuda_t list option
  =
  match expr with
  | Literal lit -> Literal lit, structureMap, None
  | ScalarPrimitive prim -> ScalarPrimitive prim, structureMap, None
  | Ref ref -> Ref ref, structureMap, None
  | Frame { elements; dimension; type' } ->
    let elements, newMapStructure, index = tryToParallelizeList elements structureMap in
    Frame { elements; dimension; type' }, newMapStructure, index
  | BoxValue { box; type' } ->
    let newBox, newMapStructure, index = tryToParallelize box structureMap in
    BoxValue { box = newBox; type' }, newMapStructure, index
  | IndexLet { indexArgs; body; type' } ->
    let tArgs =
      List.map
        ~f:(fun { indexValue; indexBinding = _; sort = _ } ->
          match indexValue with
          | Runtime t -> t
          | FromBox { box; i = _ } -> box)
        indexArgs
    in
    let result, newStructureMap, index =
      tryToParallelizeList (body :: tArgs) structureMap
    in
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
    IndexLet { indexArgs = newArgs; body = newBody; type' }, newStructureMap, index
  | ReifyIndex ri -> ReifyIndex ri, structureMap, None
  | ShapeProd sp -> ShapeProd sp, structureMap, None
  | Let { args; body; type' } ->
    let argValues = List.map ~f:(fun { binding = _; value } -> value) args in
    let result, newStructureMap, index =
      tryToParallelizeList (body :: argValues) structureMap
    in
    let newBody = List.hd_exn result in
    let newArgsValues = List.tl_exn result in
    let newArgs =
      List.map2_exn args newArgsValues ~f:(fun { binding; value = _ } value ->
        Nested.Expr.{ binding; value })
    in
    Let { args = newArgs; body = newBody; type' }, newStructureMap, index
  | LoopBlock lb ->
    let _, innerStructureMap, bodyIndex = tryToParallelize lb.mapBody structureMap in
    let result =
      IndexingModeDrafting.ParallelizationStructureCUDA.tryToParallelize
        innerStructureMap
        lb
    in
    (* Stdio.print_endline
       (Printf.sprintf
       "Dealing with loopblock: \n%s"
       (Sexp.to_string_hum ([%sexp_of: Nested.Expr.loopBlock] lb))); *)
    (match result with
     | None -> Stdio.print_endline "Did not par loopblock"
     | Some (structure, indexThing) ->
       Stdio.print_endline
         (Printf.sprintf
            "Par loop block map: \nStructure: \n%s\nIndex:\n%s"
            (Sexp.to_string_hum ([%sexp_of: IndexingModeDrafting.cuda_t] structure))
            (Sexp.to_string_hum
               ([%sexp_of: IndexingModeDrafting.ParallelizationStructureCUDA.indexMode]
                  indexThing))));
    let mergeWithBodyIndex index =
      match bodyIndex with
      | None -> [ index ]
      | Some bodyIndex -> index :: bodyIndex
    in
    (match result with
     | None -> LoopBlock lb, structureMap, None
     | Some (structure, index) ->
       let mergedIndex = mergeWithBodyIndex index in
       let structureMap =
         IndexingModeDrafting.updateStructureWithIndexMode structure index
       in
       LoopBlock lb, structureMap, Some mergedIndex)
  | Box { indices; body; bodyType; type' } ->
    let newBody, newStructureMap, index = tryToParallelize body structureMap in
    Box { body = newBody; indices; bodyType; type' }, newStructureMap, index
  | Values { elements; type' } ->
    let newElements, newStructureMap, index =
      tryToParallelizeList elements structureMap
    in
    Values { elements = newElements; type' }, newStructureMap, index
  | TupleDeref { tuple; index; type' } ->
    let newTuple, newStructureMap, index_loop = tryToParallelize tuple structureMap in
    TupleDeref { tuple = newTuple; index; type' }, newStructureMap, index_loop
  | ContiguousSubArray { arrayArg; indexArg; originalShape; resultShape; type' } ->
    let argResult, newStructureMap, index =
      tryToParallelizeList [ arrayArg; indexArg ] structureMap
    in
    let newArrayArg = List.nth_exn argResult 0 in
    let newIndexArg = List.nth_exn argResult 1 in
    ( ContiguousSubArray
        { arrayArg = newArrayArg
        ; indexArg = newIndexArg
        ; originalShape
        ; resultShape
        ; type'
        }
    , newStructureMap
    , index )
  | Append { args; type' } ->
    let newArgs, newStructureMap, index = tryToParallelizeList args structureMap in
    Append { args = newArgs; type' }, newStructureMap, index
  | Zip { zipArg; nestCount; type' } ->
    let newZipArg, newStructureMap, index = tryToParallelize zipArg structureMap in
    Zip { zipArg = newZipArg; nestCount; type' }, newStructureMap, index
  | Unzip { unzipArg; type' } ->
    let newUnzipArg, newStructureMap, index = tryToParallelize unzipArg structureMap in
    Unzip { unzipArg = newUnzipArg; type' }, newStructureMap, index

and tryToParallelizeList
  (elements : Nested.t list)
  (structureMap : IndexingModeDrafting.cuda_t)
  : Nested.t list
    * IndexingModeDrafting.cuda_t
    * IndexingModeDrafting.index_cuda_t list option
  =
  match elements with
  | [] -> elements, structureMap, None
  | hd :: tl ->
    let _, _, index = tryToParallelize hd structureMap in
    let index =
      List.fold tl ~init:index ~f:(fun indexAcc e ->
        let _, _, index = tryToParallelize e structureMap in
        match index, indexAcc with
        | None, None -> None
        | Some i, None | None, Some i -> Some i
        | Some i1, Some i2 -> Some (IndexingModeDrafting.mergeIndexModeTrees i1 i2))
    in
    let newStructureMap =
      match index with
      | None -> structureMap
      | Some index ->
        IndexingModeDrafting.updateStructureWithIndexModeTree structureMap index
    in
    newStructureMap
    |> [%sexp_of: IndexingModeDrafting.cuda_t]
    |> Sexp.to_string_hum
    |> Printf.sprintf "Structure pair after merging: %s"
    |> Stdio.print_endline;
    elements, newStructureMap, index
;; *)

type parPath =
  { indexModeTree : IndexingModeDrafting.index_tree_cuda_t
  ; inner : int
  ; extensible : bool
  }
[@@deriving sexp_of]

let rec findAllParOptions (expr : Nested.t) (structureMap : IndexingModeDrafting.cuda_t)
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
    let innerIterSpace = getIterationSpace lb.mapBody in
    let innerPaths =
      match innerPaths with
      | [] ->
        [ { indexModeTree = IndexingModeDrafting.emptyIndexTree
          ; inner = innerIterSpace
          ; extensible = true
          }
        ]
      | innerPaths -> innerPaths
    in
    (* Stdio.print_endline *)
    (*   (Printf.sprintf "Calculating new paths, we start with %d" (List.length innerPaths)); *)
    let newPossiblePaths =
      List.concat_map innerPaths ~f:(fun { indexModeTree; inner; extensible } ->
        let structureMap =
          IndexingModeDrafting.updateStructureWithIndexModeTree structureMap indexModeTree
        in
        (* (indexModeTree, structureMap) *)
        (* |> [%sexp_of: *)
        (*      IndexingModeDrafting.index_tree_cuda_t * IndexingModeDrafting.cuda_t] *)
        (* |> Sexp.to_string_hum *)
        (* |> Printf.sprintf "Index tree and structure map: %s" *)
        (* |> Stdio.print_endline; *)
        let loopBlockPar = IndexingModeDrafting.tryToParallelizeCUDA structureMap lb in
        match loopBlockPar with
        | None -> [ { indexModeTree; inner; extensible = false } ]
        | Some loopBlockIndex ->
          let loopBlockIndex =
            IndexingModeDrafting.createIndexModeAlloc
              ~label:lb.label
              ~indexMode:loopBlockIndex
          in
          if not extensible
          then [ { indexModeTree; inner; extensible } ]
          else if not (IndexingModeDrafting.hasBeenParallelized indexModeTree)
          then (
            (* Stdio.print_endline "Working on unparred path"; *)
            (*we haven't done par on this path*)
            let dontPar = { indexModeTree; inner; extensible } in
            let extTreeOpt =
              IndexingModeDrafting.appendIndexToTree [ loopBlockIndex ] indexModeTree
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
              [ dontPar; startPar ])
          else (
            let extTreeOpt =
              IndexingModeDrafting.appendIndexToTree [ loopBlockIndex ] indexModeTree
            in
            match extTreeOpt with
            | None -> raise Unimplemented.default
            | Some tree ->
              let continuePar = { indexModeTree = tree; inner; extensible } in
              let stopPar = { indexModeTree; inner; extensible = false } in
              [ continuePar; stopPar ]))
    in
    (* newPossiblePaths *)
    (* |> [%sexp_of: parPath list] *)
    (* |> Sexp.to_string_hum *)
    (* |> Printf.sprintf "New possiblePaths: \n%s" *)
    (* |> Stdio.print_endline; *)
    (* innerPaths *)
    (* |> [%sexp_of: parPath list] *)
    (* |> Sexp.to_string_hum *)
    (* |> Printf.sprintf "innerPaths: \n%s" *)
    (* |> Stdio.print_endline; *)
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

and findAllParOptionsList
  (elements : Nested.t list)
  (structureMap : IndexingModeDrafting.cuda_t)
  : Nested.t list * parPath list
  =
  match elements with
  | [] -> elements, []
  | elements ->
    (* This is probably pretty suboptimal, but searching the entire space is probably too hard and
       annoying (from data design perspective) *)
    (* TODO: add Branches here*)
    let allSegmentedPaths =
      List.map elements ~f:(fun e ->
        let _, paths = findAllParOptions e structureMap in
        paths)
    in
    let branchedApproach =
      List.filter_map allSegmentedPaths ~f:(fun paths ->
        if List.is_empty paths
        then None
        else (
          let bestPath =
            List.fold (List.tl_exn paths) ~init:(List.hd_exn paths) ~f:(fun best path ->
              let newBest =
                IndexingModeDrafting.compareStructures
                  best.indexModeTree
                  path.indexModeTree
                  best.inner
                  path.inner
              in
              match newBest with
              | None -> best
              | Some newBest ->
                let newInner =
                  if IndexingModeDrafting.equal_index_tree_cuda_t
                       newBest
                       best.indexModeTree
                  then path.inner
                  else best.inner
                in
                { indexModeTree = newBest; inner = newInner; extensible = false })
          in
          Some bestPath))
    in
    let branchPathTree =
      IndexingModeDrafting.ParallelizationStructureCUDA.Branches
        (List.map branchedApproach ~f:(fun b -> b.indexModeTree))
    in
    let branchTreeInner =
      List.fold branchedApproach ~init:0 ~f:(fun acc b -> acc + b.inner)
    in
    let branchPath =
      { indexModeTree = branchPathTree; inner = branchTreeInner; extensible = false }
    in
    let allPaths = List.concat allSegmentedPaths in
    let extensiblePaths, nonExtensiblePaths =
      List.partition_tf allPaths ~f:(fun { indexModeTree = _; inner = _; extensible } ->
        extensible)
    in
    (* i don't have a good explanations why these two are different but
       from what i can tell, you wanna choose from 'completed' paths
       but for non-complete, you want to merge instead because you might grow it further *)
    let bestExtensiblePath =
      match extensiblePaths with
      | [] -> []
      | hd :: tl ->
        let bestPath =
          List.fold tl ~init:hd ~f:(fun best path ->
            match best.indexModeTree, path.indexModeTree with
            | FullPar bestTree, FullPar pathTree ->
              let newBest =
                IndexingModeDrafting.mergeIndexModeAllocTrees bestTree pathTree
              in
              { indexModeTree = FullPar newBest
              ; inner = Int.max best.inner path.inner
              ; extensible = true
              }
            | _ -> raise Unimplemented.default)
        in
        [ bestPath ]
    in
    let bestNonExtensiblePath =
      if List.is_empty nonExtensiblePaths
      then []
      else (
        let bestPath =
          List.fold
            (List.tl_exn nonExtensiblePaths)
            ~init:(List.hd_exn nonExtensiblePaths)
            ~f:(fun best path ->
              let newBest =
                IndexingModeDrafting.compareStructures
                  best.indexModeTree
                  path.indexModeTree
                  best.inner
                  path.inner
              in
              match newBest with
              | None -> best
              | Some newBest ->
                let newInner =
                  if IndexingModeDrafting.equal_index_tree_cuda_t
                       newBest
                       best.indexModeTree
                  then best.inner
                  else path.inner
                in
                { indexModeTree = newBest; inner = newInner; extensible = false })
        in
        [ bestPath ])
    in
    elements, branchPath :: List.append bestExtensiblePath bestNonExtensiblePath
;;

let tableFromPath =
  let open IndexingModeDrafting.ParallelizationStructureCUDA in
  let rec tableFromPathHelper table = function
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
  (loopBlockParTable : (Identifier.t, IndexingModeDrafting.index_cuda_t, _) Map.t)
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
  (* | LoopBlock *)
  (*     { frameShape *)
  (*     ; label *)
  (*     ; mapArgs *)
  (*     ; mapIotas *)
  (*     ; mapBody *)
  (*     ; mapBodyMatcher *)
  (*     ; mapResults *)
  (*     ; consumer = None *)
  (*     ; type' *)
  (*     } -> *)
  (*   let indexMode = Map.find loopBlockParTable label in *)
  (*   let mapBody = exprToMapBody mapBody loopBlockParTable in *)
  (*   let type' = Type.Tuple type' in *)
  (*   let mapKernel : Corn.Expr.mapKernel = *)
  (*     { frameShape *)
  (*     ; indexMode *)
  (*     ; mapArgs *)
  (*     ; mapIotas *)
  (*     ; mapBody *)
  (*     ; mapBodyMatcher *)
  (*     ; mapResults *)
  (*     ; type' *)
  (*     } *)
  (*   in *)
  (*   MapBodySubMap (MapBodyMap mapKernel) *)
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
  (* let open KernelizeState.Let_syntax in *)
  (* Stdio.prerr_endline "Fuse and Simplify done"; *)
  let loopStructure = extractLoopStructure expr in
  Stdio.print_endline
    (Printf.sprintf
       "Loop structure: \n%s"
       (Sexp.to_string_hum ([%sexp_of: loopStructureTree] loopStructure)));
  let _, paths = findAllParOptions expr IndexingModeDrafting.defaultCUDA in
  (* let _, _, index = tryToParallelize expr IndexingModeDrafting.defaultCUDA in*)
  let bestPath =
    match paths with
    | [] -> raise Unimplemented.default
    | hd :: tl ->
      List.fold tl ~init:hd ~f:(fun best path ->
        let newBest =
          IndexingModeDrafting.compareStructures
            best.indexModeTree
            path.indexModeTree
            best.inner
            path.inner
        in
        match newBest with
        | None -> best
        | Some newBest ->
          let newInner =
            if IndexingModeDrafting.equal_index_tree_cuda_t newBest best.indexModeTree
            then best.inner
            else path.inner
          in
          { indexModeTree = newBest; inner = newInner; extensible = false })
  in
  paths
  |> [%sexp_of: parPath list]
  |> Sexp.to_string_hum
  |> Printf.sprintf "Resulting index: %s"
  |> Stdio.print_endline;
  bestPath
  |> [%sexp_of: parPath]
  |> Sexp.to_string_hum
  |> Printf.sprintf "Best path %s"
  |> Stdio.print_endline;
  let loopBlockParTable = tableFromPath bestPath.indexModeTree in
  let newExpr : Corn.t = rewriteWithPar expr loopBlockParTable in
  (* newExpr *)
  (* |> [%sexp_of: host Corn.Expr.t] *)
  (* |> Sexp.to_string_hum *)
  (* |> Printf.sprintf "new expr:\n%s" *)
  (* |> Stdio.print_endline; *)
  (* let%map opts = getOpts expr in opts.hostExpr *)
  Stdio.prerr_endline "Kernelize done";
  State.return newExpr
;;

(* newExpr *)

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
