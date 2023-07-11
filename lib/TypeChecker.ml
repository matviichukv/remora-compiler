open! Base
open Ast
open Source

type 't expectedActual =
  { expected : 't
  ; actual : 't
  }

type error =
  | UnboundIndexVariable of string
  | UnexpectedSort of
      { expected : Sort.t
      ; actual : Sort.t
      }
  | DuplicateTypeParameterName of string
  | UnboundTypeVariable of string
  | UnexpectedKind of
      { expected : Kind.t
      ; actual : Kind.t
      }
  | DuplicateIndexParameterName of string
  | UnboundVariable of string
  | DuplicateParameterName of string
  | WrongNumberOfElementsInArray of int expectedActual
  | WrongNumberOfArraysInFrame of int expectedActual
  | WrongNumberOfElementsInBoxes of int expectedActual
  | ArrayTypeDisagreement of
      { firstElementType : Typed.Type.t
      ; gotElementType : Typed.Type.t
      }
  | FrameTypeDisagreement of
      { firstArrayType : Typed.Type.t
      ; gotArrayType : Typed.Type.t
      }
  | SigmaBodyTypeDisagreement of Typed.Type.t expectedActual
  | ExpectedAtomicExpr of { actual : Typed.Type.t }
  | ExpectedArrType of { actual : Typed.Type.t }
  | ExpectedTupleType of { actual : Typed.Type.t }
  | ExpectedSigmaType of { actual : Typed.Type.t }
  | ExpectedFuncType of { actual : Typed.Type.t }
  | ExpectedValue
  | ExpectedForall of { actual : Typed.Type.t }
  | WrongNumberOfArguments of int expectedActual
  | WrongNumberOfBindings of int expectedActual
  | WrongNumberOfUnboxParameters of int expectedActual
  | DuplicateTupleBindingName of string
  | LetTypeDisagreement of Typed.Type.t expectedActual
  | TupleLetTypeDisagreement of Typed.Type.t expectedActual
  | UnexpectedSortBoundInUnbox of Sort.t expectedActual
  | EscapingRef of string
  | ArgumentTypeDisagreement of Typed.Type.t expectedActual
  | CellShapeDisagreement of Typed.Index.shape expectedActual
  | PrincipalFrameDisagreement of Typed.Index.shape expectedActual

module Show : sig
  val sort : Sort.t -> string
  val kind : Kind.t -> string
  val shape : Typed.Index.shape -> string
  val type' : Typed.Type.t -> string
end = struct
  let sort = function
    | Sort.Dim -> "Dim"
    | Sort.Shape -> "Shape"
  ;;

  let kind = function
    | Kind.Atom -> "Atom"
    | Kind.Array -> "Array"
  ;;

  let showDimension ({ const; refs } : Typed.Index.dimension) =
    let constElement = if const = 0 then None else Some (Int.to_string const) in
    let refElements =
      refs
      |> Map.to_alist
      |> List.bind ~f:(fun (id, count) -> List.init count ~f:(fun _ -> Some id.name))
    in
    let elements = constElement :: refElements |> List.filter_opt in
    match elements with
    | [] -> "0"
    | [ e ] -> e
    | elems ->
      let joinedElems = String.concat ~sep:" " elems in
      [%string "(+ %{joinedElems})"]
  ;;

  let showShapeElement = function
    | Typed.Index.Add dim -> showDimension dim
    | Typed.Index.ShapeRef ref -> ref.name
  ;;

  let showList ?(prependSpace = false) shower list =
    if prependSpace
    then list |> List.bind ~f:(fun e -> [ " "; shower e ]) |> String.concat
    else list |> List.map ~f:shower |> String.concat ~sep:" "
  ;;

  let shape elements = [%string "[%{showList showShapeElement elements}]"]
  let showParam (p : 't Typed.param) = p.binding.name

  let rec showArray =
    let open Typed.Type in
    function
    | ArrayRef ref -> ref.name
    | Arr { element; shape } ->
      if List.is_empty shape
      then showAtom element
      else (
        let shapeString = showList ~prependSpace:true showShapeElement shape in
        [%string "[%{showAtom element}%{shapeString}]"])

  and showAtom =
    let open Typed.Type in
    function
    | AtomRef ref -> ref.name
    | Func { parameters; return } ->
      [%string "(→ (%{showList showArray parameters}) %{showArray return})"]
    | Forall { parameters; body } ->
      let paramsString = parameters |> showList showParam in
      [%string "(∀ (%{paramsString}) %{showArray body})"]
    | Pi { parameters; body } ->
      let paramsString = parameters |> showList showParam in
      [%string "(Π (%{paramsString}) %{showArray body})"]
    | Sigma { parameters; body } ->
      let paramsString = parameters |> showList showParam in
      [%string "(Σ (%{paramsString}) %{showArray body})"]
    | Tuple [ element ] -> [%string "(%{showAtom element} *)"]
    | Tuple elements ->
      let elementsString = elements |> List.map ~f:showAtom |> String.concat ~sep:" * " in
      [%string "(%{elementsString})"]
    | Literal Integer -> "int"
    | Literal Character -> "char"

  and type' : Typed.Type.t -> string = function
    | Array array -> showArray array
    | Atom atom -> showAtom atom
  ;;
end

let errorMessage = function
  | UnboundIndexVariable name -> [%string "Unbound index variable `%{name}`"]
  | UnboundTypeVariable name -> [%string "Unbound type variable `%{name}`"]
  | UnboundVariable name -> [%string "Unbound variable `%{name}`"]
  | UnexpectedSort { expected; actual } ->
    [%string
      "Unexpected sort: expected `%{Show.sort expected}`, got `%{Show.sort actual}`"]
  | UnexpectedKind { expected; actual } ->
    [%string
      "Unexpected sort: expected `%{Show.kind expected}`, got `%{Show.kind actual}`"]
  | DuplicateTypeParameterName name -> [%string "Duplicate type parameter name `%{name}`"]
  | DuplicateIndexParameterName name ->
    [%string "Duplicate index parameter name `%{name}`"]
  | DuplicateParameterName name -> [%string "Duplicate parameter name `%{name}`"]
  | WrongNumberOfElementsInArray { expected; actual } ->
    [%string "Expected %{expected#Int} elements in array, got %{actual#Int}"]
  | WrongNumberOfArraysInFrame { expected; actual } ->
    [%string "Expected %{expected#Int} arrays in frame, got %{actual#Int}"]
  | WrongNumberOfElementsInBoxes { expected; actual } ->
    [%string "Expected %{expected#Int} elements in boxes, got %{actual#Int}"]
  | ArrayTypeDisagreement { firstElementType; gotElementType } ->
    [%string
      "Mismatched array elements; first element is type `%{Show.type' \
       firstElementType}`, got `%{Show.type' gotElementType}`"]
  | FrameTypeDisagreement { firstArrayType; gotArrayType } ->
    [%string
      "Mismatched frame arrays; first array is type `%{Show.type' firstArrayType}`, got \
       `%{Show.type' gotArrayType}`"]
  | SigmaBodyTypeDisagreement { expected; actual } ->
    [%string "Expected type `%{Show.type' expected}`, got `%{Show.type' actual}`"]
  | ExpectedAtomicExpr { actual } ->
    [%string "Expected atomic expression, got type `%{Show.type' actual}`"]
  | ExpectedArrType { actual } ->
    [%string "Expected an Arr type, got `%{Show.type' actual}`"]
  | ExpectedTupleType { actual } ->
    [%string "Expected a Tuple type, got `%{Show.type' actual}`"]
  | ExpectedSigmaType { actual } ->
    [%string "Expected a Sigma type, got `%{Show.type' actual}`"]
  | ExpectedFuncType { actual } ->
    [%string "Expected a function type, got `%{Show.type' actual}`"]
  | ExpectedValue -> "Expected a value"
  | ExpectedForall { actual } ->
    [%string "Expected an express with a Forall type, got `%{Show.type' actual}`"]
  | WrongNumberOfArguments { expected; actual } ->
    [%string "Expected %{expected#Int} arguements, got %{actual#Int}"]
  | WrongNumberOfBindings { expected; actual } ->
    [%string "Expected %{expected#Int} bindings for tuple, got %{actual#Int}"]
  | WrongNumberOfUnboxParameters { expected; actual } ->
    [%string "Expected %{expected#Int} parameters for unboxing, got %{actual#Int}"]
  | DuplicateTupleBindingName name -> [%string "Duplicate variable name `%{name}`"]
  | LetTypeDisagreement { expected; actual } ->
    [%string
      "Let expected a value of type `%{Show.type' expected}`, got `%{Show.type' actual}`"]
  | TupleLetTypeDisagreement { expected; actual } ->
    [%string
      "Tuple-Let expected an element of type `%{Show.type' expected}`, got `%{Show.type' \
       actual}`"]
  | UnexpectedSortBoundInUnbox { expected; actual } ->
    [%string
      "Unexpected bound: expected `%{Show.sort expected}`, got `%{Show.sort actual}`"]
  | EscapingRef ref -> [%string "The variable `%{ref}` escapes the box context"]
  | ArgumentTypeDisagreement { expected; actual } ->
    [%string
      "Function expected argument with element type `%{Show.type' expected}`, got \
       `%{Show.type' actual}`"]
  | CellShapeDisagreement { expected; actual } ->
    [%string
      "Function expected argument with cell shape `%{Show.shape expected}`, got \
       `%{Show.shape actual}`"]
  | PrincipalFrameDisagreement { expected; actual } ->
    [%string
      "Function call has principal frame `%{Show.shape expected}`, got frame \
       `%{Show.shape actual}`"]
;;

let errorType = function
  | UnboundIndexVariable _ | UnexpectedSort _ -> `Sort
  | UnboundTypeVariable _
  | UnexpectedKind _
  | DuplicateTypeParameterName _
  | DuplicateIndexParameterName _ -> `Kind
  | UnboundVariable _
  | DuplicateParameterName _
  | WrongNumberOfElementsInArray _
  | WrongNumberOfArraysInFrame _
  | WrongNumberOfElementsInBoxes _
  | ArrayTypeDisagreement _
  | FrameTypeDisagreement _
  | SigmaBodyTypeDisagreement _
  | ExpectedAtomicExpr _
  | ExpectedArrType _
  | ExpectedTupleType _
  | ExpectedSigmaType _
  | ExpectedFuncType _
  | ExpectedValue
  | ExpectedForall _
  | WrongNumberOfArguments _
  | WrongNumberOfBindings _
  | WrongNumberOfUnboxParameters _
  | DuplicateTupleBindingName _
  | LetTypeDisagreement _
  | TupleLetTypeDisagreement _
  | UnexpectedSortBoundInUnbox _
  | EscapingRef _
  | ArgumentTypeDisagreement _
  | CellShapeDisagreement _
  | PrincipalFrameDisagreement _ -> `Type
;;

type ('s, 't) checkResult = ('t, ('s, error) Source.annotate) MResult.t
type state = { idCounter : int }

module CheckerStateT = struct
  include StateT.Make2WithError (MResult)

  type nonrec state = state

  let ok = return
  let err error = returnF (MResult.err error)
  let errs errors = returnF (MResult.Errors errors)

  let ofOption o ~err:error =
    match o with
    | Some v -> return v
    | None -> err error
  ;;

  let require b error = if b then return () else err error

  let traverseOpt = function
    | Some r -> map r ~f:(fun e -> Some e)
    | None -> return None
  ;;

  let createId name =
    make ~f:(fun state ->
        ( { idCounter = state.idCounter + 1 }
        , Typed.Identifier.{ name; id = state.idCounter + 1 } ))
  ;;
end

open CheckerStateT.Let_syntax

let ok = CheckerStateT.ok

type ('s, 't) checkerStateT = (state, 't, ('s, error) Source.annotate) CheckerStateT.t

type ('t, 'u) processedParams =
  { typedParams : 't Typed.param list
  ; extendedEnv : 'u Environment.entry Map.M(String).t
  }

type ('s, 't, 'u) paramsToMapResult =
  { typedParamsReversed : 't Typed.param list
  ; entries : 'u Environment.entry Map.M(String).t
  ; dups : 's Map.M(String).t
  }

(** Extend the environment with the bindings specified by the parameters,
    and convert the untyped parameters into typed parameters. Any duplicate
    parameter names are detected and converted into erros via makeError *)
let processParams env params ~makeError ~boundToEnvEntry
    : ('s, ('t, 'u) processedParams) checkerStateT
  =
  (* Loops over the params, creating environment entries, converting into
      typed params, and detecting duplicates *)
  let rec collapseParams
      (params : ('s, ('s, 't) Untyped.param) Source.annotate list)
      (acc : ('s, ('s, 't, 'u) paramsToMapResult) checkerStateT)
      : ('s, ('s, 't, 'u) paramsToMapResult) checkerStateT
    =
    match params with
    | [] -> acc
    | { elem = { binding; bound }; source = _ } :: rest ->
      let name = binding.elem in
      let%bind { typedParamsReversed = oldParams; entries = oldEntries; dups = oldDups } =
        acc
      in
      let%bind id = CheckerStateT.createId name in
      let typedParam : 't Typed.param = { binding = id; bound } in
      let newParams = typedParam :: oldParams in
      let entry = Environment.{ e = boundToEnvEntry bound; id = typedParam.binding } in
      (match Map.add oldEntries ~key:name ~data:entry with
      | `Ok newEntries ->
        collapseParams
          rest
          (ok { typedParamsReversed = newParams; entries = newEntries; dups = oldDups })
      | `Duplicate ->
        let newDups = Map.set oldDups ~key:name ~data:binding.source in
        collapseParams
          rest
          (ok { typedParamsReversed = newParams; entries = oldEntries; dups = newDups }))
  in
  let%bind { typedParamsReversed; entries; dups } =
    collapseParams
      params
      (ok
         { typedParamsReversed = []
         ; entries = Map.empty (module String)
         ; dups = Map.empty (module String)
         })
  in
  let typedParams = List.rev typedParamsReversed in
  match NeList.of_list (Map.to_alist dups) with
  | None ->
    let extendedEnv =
      Map.merge_skewed env entries ~combine:(fun ~key:_ _ newEntry -> newEntry)
    in
    ok { typedParams; extendedEnv }
  | Some dups ->
    CheckerStateT.errs
      (NeList.map dups ~f:(fun (name, source) -> { elem = makeError name; source }))
;;

module SortChecker = struct
  let rec check (env : Environment.t) { elem = index; source } =
    let module U = Untyped.Index in
    let module T = Typed.Index in
    match index with
    | U.Ref name ->
      Map.find env.sorts name
      |> Option.map ~f:(fun entry ->
             match entry.e with
             | Sort.Dim -> T.Dimension (T.dimensionRef entry.id)
             | Sort.Shape -> T.Shape [ T.ShapeRef entry.id ])
      |> CheckerStateT.ofOption ~err:{ source; elem = UnboundIndexVariable name }
    | U.Dimension dim -> ok (T.Dimension (T.dimensionConstant dim))
    | U.Shape indices ->
      let%map indices = CheckerStateT.all (List.map indices ~f:(checkAndExpectDim env)) in
      T.Shape (List.map ~f:(fun d -> T.Add d) indices)
    | U.Add indices ->
      let%map indices = CheckerStateT.all (List.map indices ~f:(checkAndExpectDim env)) in
      let flattenedDimension =
        indices
        |> List.fold_left
             ~init:
               ({ const = 0; refs = Map.empty (module Typed.Identifier) } : T.dimension)
             ~f:(fun m1 m2 ->
               { const = m1.const + m2.const
               ; refs =
                   Map.merge_skewed m1.refs m2.refs ~combine:(fun ~key:_ a b -> a + b)
               })
      in
      T.Dimension flattenedDimension
    | U.Append indices ->
      let%map nestedIndices =
        indices |> List.map ~f:(checkAndExpectShape env) |> CheckerStateT.all
      in
      let indices = List.join nestedIndices in
      T.Shape indices

  and checkAndExpectDim env index =
    match%bind check env index with
    | Typed.Index.Dimension d -> ok d
    | Typed.Index.Shape _ ->
      CheckerStateT.err
        { source = index.source
        ; elem = UnexpectedSort { expected = Sort.Dim; actual = Sort.Shape }
        }

  and checkAndExpectShape env index =
    match%bind check env index with
    | Typed.Index.Dimension _ ->
      CheckerStateT.err
        { source = index.source
        ; elem = UnexpectedSort { expected = Sort.Dim; actual = Sort.Shape }
        }
    | Typed.Index.Shape s -> ok s
  ;;

  let checkAndExpect sort env index =
    match sort with
    | Sort.Dim -> checkAndExpectDim env index >>| fun r -> Typed.Index.Dimension r
    | Sort.Shape -> checkAndExpectShape env index >>| fun r -> Typed.Index.Shape r
  ;;
end

module KindChecker = struct
  let rec check (env : Environment.t) { elem = type'; source } =
    let module U = Untyped.Type in
    let module T = Typed.Type in
    match type' with
    | U.Ref name ->
      Map.find env.kinds name
      |> Option.map ~f:(fun entry ->
             match entry.e with
             | Kind.Array -> T.Array (T.ArrayRef entry.id)
             | Kind.Atom -> T.Atom (T.AtomRef entry.id))
      |> CheckerStateT.ofOption ~err:{ source; elem = UnboundTypeVariable name }
    | U.Arr { element; shape } ->
      let%map element = checkAndExpectAtom env element
      and shape = SortChecker.checkAndExpectShape env shape in
      T.Array (T.Arr { element; shape })
    | U.Func { parameters; return } ->
      let%map parameters =
        parameters.elem |> List.map ~f:(checkAndExpectArray env) |> CheckerStateT.all
      and return = checkAndExpectArray env return in
      T.Atom (T.Func { parameters; return })
    | U.Forall { parameters; body } ->
      let parameters =
        (* The parameter's have source-annotated bounds; remove the source annotations *)
        List.map parameters.elem ~f:(function
            | { elem = { binding; bound = { elem = bound; source = _ } }; source } ->
            { elem = ({ binding; bound } : ('s, Kind.t) Untyped.param); source })
      in
      let%bind { typedParams = parameters; extendedEnv = extendedKinds } =
        processParams
          env.kinds
          parameters
          ~makeError:(fun name -> DuplicateTypeParameterName name)
          ~boundToEnvEntry:(fun b -> b)
      in
      let extendedEnv = { env with kinds = extendedKinds } in
      let%map body = checkAndExpectArray extendedEnv body in
      T.Atom (T.Forall { parameters; body })
    | U.Pi { parameters; body } ->
      let parameters =
        (* The parameter's have source-annotated bounds; remove the source annotations *)
        List.map parameters.elem ~f:(function
            | { elem = { binding; bound = { elem = bound; source = _ } }; source } ->
            { elem = ({ binding; bound } : ('s, Sort.t) Untyped.param); source })
      in
      let%bind { typedParams = parameters; extendedEnv = extendeSorts } =
        processParams
          env.sorts
          parameters
          ~makeError:(fun name -> DuplicateIndexParameterName name)
          ~boundToEnvEntry:(fun b -> b)
      in
      let extendedEnv = { env with sorts = extendeSorts } in
      let%map body = checkAndExpectArray extendedEnv body in
      T.Atom (T.Pi { parameters; body })
    | U.Sigma { parameters; body } ->
      let parameters =
        (* The parameter's have source-annotated bounds; remove the source annotations *)
        List.map parameters.elem ~f:(function
            | { elem = { binding; bound = { elem = bound; source = _ } }; source } ->
            { elem = ({ binding; bound } : ('s, Sort.t) Untyped.param); source })
      in
      let%bind { typedParams = parameters; extendedEnv = extendeSorts } =
        processParams
          env.sorts
          parameters
          ~makeError:(fun name -> DuplicateIndexParameterName name)
          ~boundToEnvEntry:(fun b -> b)
      in
      let extendedEnv = { env with sorts = extendeSorts } in
      let%map body = checkAndExpectArray extendedEnv body in
      T.Atom (T.Sigma { parameters; body })
    | U.Tuple elements ->
      let%map kindedElements =
        elements |> List.map ~f:(checkAndExpectAtom env) |> CheckerStateT.all
      in
      T.Atom (T.Tuple kindedElements)

  and checkAndExpectArray env type' =
    let open Typed.Type in
    match%bind check env type' with
    | Array array -> ok array
    | Atom atom -> ok (Arr { element = atom; shape = [] })

  and checkAndExpectAtom env type' =
    let open Typed.Type in
    match%bind check env type' with
    | Atom atom -> ok atom
    | Array _ ->
      CheckerStateT.err
        { source = type'.source
        ; elem = UnexpectedKind { expected = Kind.Atom; actual = Kind.Array }
        }
  ;;

  let checkAndExpect kind env type' =
    match kind with
    | Kind.Array -> checkAndExpectArray env type' >>| fun r -> Typed.Type.Array r
    | Kind.Atom -> checkAndExpectAtom env type' >>| fun r -> Typed.Type.Atom r
  ;;
end

module TypeChecker = struct
  let zipLists ~expected ~actual ~makeError =
    match List.zip expected actual with
    | Ok zipped -> ok zipped
    | Unequal_lengths ->
      CheckerStateT.err
        (makeError { expected = List.length expected; actual = List.length actual })
  ;;

  (** Compare two types to check that they are equal*)
  let eqType (a : Typed.Type.t) (b : Typed.Type.t) : bool =
    let open Typed in
    let universalIdCounter = ref 0 in
    let createUniversal () =
      let id = !universalIdCounter in
      universalIdCounter := !universalIdCounter + 1;
      id
    in
    let mapKeys cmp keyMap map =
      List.fold
        (Map.to_alist map)
        ~init:(Some (Map.empty cmp))
        ~f:(fun soFar (key, data) ->
          match soFar, Map.find keyMap key with
          | Some soFar, Some mappedKey -> Some (Map.set soFar ~key:mappedKey ~data)
          | _ -> None)
    in
    (* Booleans are represented as options in order to be able to use let syntax *)
    let boolToOpt = function
      | true -> Some ()
      | false -> None
    in
    let optToBool : unit option -> bool = Option.is_some in
    let open Option.Let_syntax in
    let rec compareIndices (a, aEnv) (b, bEnv) : unit option =
      let open Index in
      match a with
      | Dimension a ->
        let%bind b =
          match b with
          | Dimension b -> Some b
          | _ -> None
        in
        let%bind aRefs = mapKeys (module Int) aEnv a.refs in
        let%bind bRefs = mapKeys (module Int) bEnv b.refs in
        boolToOpt (Map.equal ( = ) aRefs bRefs)
      | Shape a ->
        let%bind b =
          match b with
          | Shape b -> Some b
          | _ -> None
        in
        let compareShapeElement (a, aEnv) (b, bEnv) : unit option =
          match a with
          | Add a ->
            let%bind b =
              match b with
              | Add b -> Some b
              | _ -> None
            in
            compareIndices (Dimension a, aEnv) (Dimension b, bEnv)
          | ShapeRef a ->
            let%bind b =
              match b with
              | ShapeRef b -> Some b
              | _ -> None
            in
            let%bind aRef = Map.find aEnv a in
            let%bind bRef = Map.find bEnv b in
            boolToOpt (aRef = bRef)
        in
        boolToOpt
          (List.equal
             (fun ae be -> optToBool (compareShapeElement (ae, aEnv) (be, bEnv)))
             a
             b)
    in
    (* Forall, Pi, and Sigma are all very similar, so compareTypeAbstractions
     pulls out this commonality*)
    let rec compareTypeAbstractions
              : 't.
                't Type.abstraction * int Map.M(Identifier).t
                -> 't Type.abstraction * int Map.M(Identifier).t
                -> ('t -> 't -> bool)
                -> unit option
      =
     fun (a, aEnv) (b, bEnv) boundEq ->
      let open Type in
      let%bind zippedParams =
        match List.zip a.parameters b.parameters with
        | Ok zp -> Some zp
        | Unequal_lengths -> None
      in
      let%bind aEnv, bEnv =
        List.fold
          zippedParams
          ~init:(Some (aEnv, bEnv))
          ~f:(fun envs (aParam, bParam) ->
            let%bind aEnv, bEnv = envs in
            let%bind () = boolToOpt (boundEq aParam.bound bParam.bound) in
            let universal = createUniversal () in
            Some
              ( Map.set aEnv ~key:aParam.binding ~data:universal
              , Map.set bEnv ~key:bParam.binding ~data:universal ))
      in
      compareTypes (Type.Array a.body, aEnv) (Type.Array b.body, bEnv)
    and compareTypes (a, aEnv) (b, bEnv) : unit option =
      let open Type in
      match a with
      | Array (ArrayRef a) ->
        let%bind b =
          match b with
          | Array (ArrayRef b) -> Some b
          | _ -> None
        in
        let%bind aRef = Map.find aEnv a in
        let%bind bRef = Map.find bEnv b in
        boolToOpt (aRef = bRef)
      | Array (Arr a) ->
        let%bind b =
          match b with
          | Array (Arr b) -> Some b
          | _ -> None
        in
        let%bind () = compareTypes (Atom a.element, aEnv) (Atom b.element, bEnv) in
        compareIndices (Index.Shape a.shape, aEnv) (Index.Shape b.shape, bEnv)
      | Atom (AtomRef a) ->
        let%bind b =
          match b with
          | Atom (AtomRef b) -> Some b
          | _ -> None
        in
        let%bind aRef = Map.find aEnv a in
        let%bind bRef = Map.find bEnv b in
        boolToOpt (aRef = bRef)
      | Atom (Func a) ->
        let%bind b =
          match b with
          | Atom (Func b) -> Some b
          | _ -> None
        in
        let%bind () =
          boolToOpt
            (List.equal
               (fun aParam bParam ->
                 optToBool (compareTypes (Array aParam, aEnv) (Array bParam, bEnv)))
               a.parameters
               b.parameters)
        in
        compareTypes (Array a.return, aEnv) (Array b.return, bEnv)
      | Atom (Forall a) ->
        let%bind b =
          match b with
          | Atom (Forall b) -> Some b
          | _ -> None
        in
        compareTypeAbstractions (a, aEnv) (b, bEnv) Kind.equal
      | Atom (Pi a) ->
        let%bind b =
          match b with
          | Atom (Pi b) -> Some b
          | _ -> None
        in
        compareTypeAbstractions (a, aEnv) (b, bEnv) Sort.equal
      | Atom (Sigma a) ->
        let%bind b =
          match b with
          | Atom (Sigma b) -> Some b
          | _ -> None
        in
        compareTypeAbstractions (a, aEnv) (b, bEnv) Sort.equal
      | Atom (Tuple a) ->
        let%bind b =
          match b with
          | Atom (Tuple b) -> Some b
          | _ -> None
        in
        boolToOpt
          (List.equal
             (fun aParam bParam ->
               optToBool (compareTypes (Atom aParam, aEnv) (Atom bParam, bEnv)))
             a
             b)
      | Atom (Literal Integer) ->
        (match b with
        | Atom (Literal Integer) -> Some ()
        | _ -> None)
      | Atom (Literal Character) ->
        (match b with
        | Atom (Literal Character) -> Some ()
        | _ -> None)
    in
    let result : unit option =
      compareTypes (a, Map.empty (module Identifier)) (b, Map.empty (module Identifier))
    in
    (* Convert from option back to boolean *)
    optToBool result
  ;;

  let requireType ~expected ~actual ~makeError =
    if eqType expected actual
    then ok ()
    else CheckerStateT.err (makeError { expected; actual })
  ;;

  let checkForArrType source type' =
    let open Typed.Type in
    match type' with
    | Arr arr -> ok arr
    | ArrayRef _ ->
      CheckerStateT.err { source; elem = ExpectedArrType { actual = Array type' } }
  ;;

  let checkForTupleType source type' =
    let open Typed.Type in
    match type' with
    | Tuple tup -> ok tup
    | _ -> CheckerStateT.err { source; elem = ExpectedTupleType { actual = Atom type' } }
  ;;

  let checkForSigmaType source type' =
    let open Typed.Type in
    match type' with
    | Sigma sigma -> ok sigma
    | _ -> CheckerStateT.err { source; elem = ExpectedSigmaType { actual = Atom type' } }
  ;;

  let checkForFuncType source type' =
    let open Typed.Type in
    match type' with
    | Func func -> ok func
    | _ -> CheckerStateT.err { source; elem = ExpectedFuncType { actual = Atom type' } }
  ;;

  (* Check if an expr is a value. This corresponds to Val and Atval in the
   formal syntax definition *)
  let rec requireValue { elem = expr; source } =
    let open Untyped.Expr in
    let err = CheckerStateT.err { elem = ExpectedValue; source } in
    match expr with
    | Ref _ -> ok ()
    | Arr arr ->
      arr.elements.elem
      |> NeList.map ~f:requireValue
      |> CheckerStateT.allNE
      |> CheckerStateT.ignore_m
    | EmptyArr _ -> err
    | Frame _ -> err
    | EmptyFrame _ -> err
    | TermApplication _ -> err
    | TypeApplication _ -> err
    | IndexApplication _ -> err
    | Unbox _ -> err
    | TermLambda _ -> ok ()
    | TypeLambda tl -> requireValue tl.body
    | IndexLambda il -> requireValue il.body
    | Boxes boxes ->
      boxes.elements.elem
      |> List.map ~f:(fun b -> requireValue b.elem.body)
      |> CheckerStateT.all_unit
    | Let _ -> err
    | TupleLet _ -> err
    | Tuple elements ->
      elements.elem
      |> List.map ~f:requireValue
      |> CheckerStateT.all
      |> CheckerStateT.ignore_m
    | IntLiteral _ -> ok ()
    | CharacterLiteral _ -> ok ()
  ;;

  let subIndicesIntoDimIndex indices ({ const; refs } : Typed.Index.dimension) =
    let open Typed.Index in
    Map.fold
      refs
      ~init:{ const; refs = Map.empty (Map.comparator_s refs) }
      ~f:(fun ~key:idBeingSubbed ~data:subMultiplier acc ->
        match Map.find indices idBeingSubbed with
        | Some (Dimension sub) ->
          (* need to combine togeth acc and sub, with sub repeated subMultiplier times *)
          let sub =
            { const = sub.const * subMultiplier
            ; refs = Map.map sub.refs ~f:(( * ) subMultiplier)
            }
          in
          let combinedConsts = acc.const + sub.const in
          let combinedRefs =
            Map.fold sub.refs ~init:acc.refs ~f:(fun ~key:ref ~data:count combinedRefs ->
                Map.update combinedRefs ref ~f:(fun prevCount ->
                    Option.value prevCount ~default:0 + count))
          in
          { const = combinedConsts; refs = combinedRefs }
        | Some (Shape _) -> acc
        | None -> acc)
  ;;

  let subIndicesIntoShapeIndex indices shape =
    let open Typed.Index in
    List.bind shape ~f:(function
        | Add dim -> [ Add (subIndicesIntoDimIndex indices dim) ]
        | ShapeRef id as ref ->
          (match Map.find indices id with
          | Some (Shape shape) -> shape
          | Some (Dimension _) -> [ ref ]
          | None -> [ ref ]))
  ;;

  let rec subIndicesIntoArrayType indices =
    let open Typed.Type in
    function
    | ArrayRef _ as ref -> ref
    | Arr { element; shape } ->
      Arr
        { element = subIndicesIntoAtomType indices element
        ; shape = subIndicesIntoShapeIndex indices shape
        }

  and subIndicesIntoAtomType indices =
    let open Typed.Type in
    function
    | AtomRef _ as ref -> ref
    | Func { parameters; return } ->
      Func { parameters; return = subIndicesIntoArrayType indices return }
    | Forall { parameters; body } ->
      Forall { parameters; body = subIndicesIntoArrayType indices body }
    | Pi { parameters; body } ->
      Pi { parameters; body = subIndicesIntoArrayType indices body }
    | Sigma { parameters; body } ->
      Sigma { parameters; body = subIndicesIntoArrayType indices body }
    | Tuple elements -> Tuple (List.map elements ~f:(subIndicesIntoAtomType indices))
    | Literal Integer -> Literal Integer
    | Literal Character -> Literal Character
  ;;

  let rec subTypesIntoArrayType types =
    let open Typed.Type in
    function
    | ArrayRef id as ref ->
      (match Map.find types id with
      | Some (Array arrayType) -> arrayType
      | Some (Atom _) -> ref
      | None -> ref)
    | Arr { element; shape } ->
      Arr { element = subTypesIntoAtomType types element; shape }

  and subTypesIntoAtomType types =
    let open Typed.Type in
    function
    | AtomRef id as ref ->
      (match Map.find types id with
      | Some (Atom atomType) -> atomType
      | Some (Array _) -> ref
      | None -> ref)
    | Func { parameters; return } ->
      Func { parameters; return = subTypesIntoArrayType types return }
    | Forall { parameters; body } ->
      Forall { parameters; body = subTypesIntoArrayType types body }
    | Pi { parameters; body } ->
      Pi { parameters; body = subTypesIntoArrayType types body }
    | Sigma { parameters; body } ->
      Sigma { parameters; body = subTypesIntoArrayType types body }
    | Tuple elements -> Tuple (List.map elements ~f:(subTypesIntoAtomType types))
    | Literal Integer -> Literal Integer
    | Literal Character -> Literal Character
  ;;

  let findEscapingRefs (env : Environment.t) type' =
    let checkIfEscaping env (ref : Typed.Identifier.t) =
      if Map.mem env ref.name then [] else [ ref ]
    in
    let rec findInIndex (env : Environment.t) =
      let open Typed.Index in
      function
      | Shape shapeElements ->
        List.bind shapeElements ~f:(function
            | Add dim -> findInIndex env (Dimension dim)
            | ShapeRef ref -> checkIfEscaping env.sorts ref)
      | Dimension { const = _; refs } ->
        Map.keys refs |> List.bind ~f:(checkIfEscaping env.sorts)
    in
    let rec findInType (env : Environment.t) =
      let open Typed.Type in
      function
      | Array (ArrayRef ref) -> checkIfEscaping env.kinds ref
      | Array (Arr { element; shape }) ->
        findInType env (Atom element) @ findInIndex env (Typed.Index.Shape shape)
      | Atom (AtomRef ref) -> checkIfEscaping env.kinds ref
      | Atom (Func { parameters; return }) ->
        List.bind parameters ~f:(fun a -> findInType env (Array a))
        @ findInType env (Array return)
      | Atom (Forall { parameters; body }) ->
        let extendedEnv =
          { env with
            kinds =
              List.fold parameters ~init:env.kinds ~f:(fun env param ->
                  Map.set
                    env
                    ~key:param.binding.name
                    ~data:{ e = param.bound; id = param.binding })
          }
        in
        findInType extendedEnv (Array body)
      | Atom (Pi { parameters; body }) ->
        let extendedEnv =
          { env with
            sorts =
              List.fold parameters ~init:env.sorts ~f:(fun env param ->
                  Map.set
                    env
                    ~key:param.binding.name
                    ~data:{ e = param.bound; id = param.binding })
          }
        in
        findInType extendedEnv (Array body)
      | Atom (Sigma { parameters; body }) ->
        let extendedEnv =
          { env with
            sorts =
              List.fold parameters ~init:env.sorts ~f:(fun env param ->
                  Map.set
                    env
                    ~key:param.binding.name
                    ~data:{ e = param.bound; id = param.binding })
          }
        in
        findInType extendedEnv (Array body)
      | Atom (Tuple elements) -> List.bind elements ~f:(fun a -> findInType env (Atom a))
      | Atom (Literal Integer) -> []
      | Atom (Literal Character) -> []
    in
    findInType env type'
  ;;

  let rec check (env : Environment.t) { elem = expr; source } =
    let module U = Untyped.Expr in
    let module T = Typed.Expr in
    match expr with
    | U.Ref name ->
      Map.find env.types name
      |> Option.map ~f:(fun entry -> T.Array (T.Ref { id = entry.id; type' = entry.e }))
      |> CheckerStateT.ofOption ~err:{ source; elem = UnboundVariable name }
    | U.Arr { dimensions; elements } ->
      let dimensions = dimensions.elem |> List.map ~f:(fun d -> d.elem) in
      let expectedElements = dimensions |> List.fold ~init:1 ~f:( * ) in
      let%bind () =
        CheckerStateT.require
          (expectedElements = NeList.length elements.elem)
          { source
          ; elem =
              WrongNumberOfElementsInArray
                { expected = expectedElements; actual = NeList.length elements.elem }
          }
      and elementsWithSource =
        elements.elem
        |> NeList.map ~f:(fun e ->
               checkAndExpectAtom env e >>| fun atom -> atom, e.source)
        |> CheckerStateT.allNE
      in
      let elements = elementsWithSource |> NeList.map ~f:(fun (e, _) -> e) in
      let ((firstElement, _) :: restElementsWithSource) = elementsWithSource in
      let%map () =
        restElementsWithSource
        |> List.map ~f:(fun (element, elementSource) ->
               requireType
                 ~expected:(T.type' (T.Atom firstElement))
                 ~actual:(T.type' (T.Atom element))
                 ~makeError:(fun { expected; actual } ->
                   { source = elementSource
                   ; elem =
                       ArrayTypeDisagreement
                         { firstElementType = expected; gotElementType = actual }
                   }))
        |> CheckerStateT.all_unit
      in
      let shape =
        List.map dimensions ~f:(fun n ->
            Typed.Index.Add (Typed.Index.dimensionConstant n))
      in
      T.Array
        (Arr
           { dimensions
           ; elements = NeList.to_list elements
           ; type' = { element = T.atomType firstElement; shape }
           })
    | U.EmptyArr { dimensions; elementType } ->
      let unwrappedDims = List.map dimensions.elem ~f:(fun n -> n.elem) in
      let hasZero = List.find unwrappedDims ~f:(( = ) 0) |> Option.is_some in
      let expectedElements = List.fold unwrappedDims ~init:1 ~f:( * ) in
      let%bind () =
        CheckerStateT.require
          hasZero
          { source = dimensions.source
          ; elem =
              WrongNumberOfElementsInArray { expected = expectedElements; actual = 0 }
          }
      in
      let%map elementType = KindChecker.checkAndExpectAtom env elementType in
      let shape =
        List.map unwrappedDims ~f:(fun n ->
            Typed.Index.Add (Typed.Index.dimensionConstant n))
      in
      T.Array
        (Frame
           { dimensions = unwrappedDims
           ; arrays = []
           ; type' = { element = elementType; shape }
           })
    | U.Frame { dimensions; elements = arrays } ->
      let dimensions = dimensions.elem |> List.map ~f:(fun d -> d.elem) in
      let expectedArrays = dimensions |> List.fold ~init:1 ~f:( * ) in
      let%bind () =
        CheckerStateT.require
          (expectedArrays = NeList.length arrays.elem)
          { source
          ; elem =
              WrongNumberOfArraysInFrame
                { expected = expectedArrays; actual = NeList.length arrays.elem }
          }
      and arraysWithSource =
        arrays.elem
        |> NeList.map ~f:(fun e ->
               checkAndExpectArray env e >>| fun atom -> atom, e.source)
        |> CheckerStateT.allNE
      in
      let typedArrays = arraysWithSource |> NeList.map ~f:(fun (e, _) -> e) in
      let ((firstArray, _) :: restArraysWithSource) = arraysWithSource in
      let%bind firstArrayType =
        checkForArrType (NeList.hd arrays.elem).source (T.arrayType firstArray)
      in
      let%map () =
        restArraysWithSource
        |> List.map ~f:(fun (array, arraySource) ->
               requireType
                 ~expected:(T.type' (T.Array firstArray))
                 ~actual:(T.type' (T.Array array))
                 ~makeError:(fun { expected; actual } ->
                   { source = arraySource
                   ; elem =
                       FrameTypeDisagreement
                         { firstArrayType = expected; gotArrayType = actual }
                   }))
        |> CheckerStateT.all_unit
      in
      let shape =
        List.map dimensions ~f:(fun n ->
            Typed.Index.Add (Typed.Index.dimensionConstant n))
        @ firstArrayType.shape
      in
      T.Array
        (T.Frame
           { dimensions
           ; arrays = NeList.to_list typedArrays
           ; type' = { element = firstArrayType.element; shape }
           })
    | U.EmptyFrame { dimensions; elementType = arrayType } ->
      let arrayTypeSource = arrayType.source in
      let unwrappedDims = List.map dimensions.elem ~f:(fun n -> n.elem) in
      let hasZero = List.find unwrappedDims ~f:(( = ) 0) |> Option.is_some in
      let expectedElements = List.fold unwrappedDims ~init:1 ~f:( * ) in
      let%map () =
        CheckerStateT.require
          hasZero
          { source = dimensions.source
          ; elem = WrongNumberOfArraysInFrame { expected = expectedElements; actual = 0 }
          }
      and arrayType =
        KindChecker.checkAndExpectArray env arrayType >>= checkForArrType arrayTypeSource
      in
      let shape =
        List.map unwrappedDims ~f:(fun n ->
            Typed.Index.Add (Typed.Index.dimensionConstant n))
        @ arrayType.shape
      in
      T.Array
        (T.Frame
           { dimensions = unwrappedDims
           ; arrays = []
           ; type' = { element = arrayType.element; shape }
           })
    | U.TermApplication { func; args } ->
      let funcSource = func.source in
      let argsSource = args.source in
      let%bind func, paramTypes, returnType, funcShape =
        let%bind func = checkAndExpectArray env func in
        let%bind funcArrType = checkForArrType funcSource (T.arrayType func) in
        let%bind arrowType = checkForFuncType funcSource funcArrType.element in
        let%map paramTypes =
          arrowType.parameters
          |> List.map ~f:(checkForArrType funcSource)
          |> CheckerStateT.all
        and returnType = checkForArrType funcSource arrowType.return in
        func, paramTypes, returnType, funcArrType.shape
      and args =
        args.elem
        |> List.map ~f:(fun arg ->
               let argSource = arg.source in
               let%bind arg = checkAndExpectArray env arg in
               let%map argType = checkForArrType argSource (T.arrayType arg) in
               arg, argType, argSource)
        |> CheckerStateT.all
      in
      let%bind zippedArgs =
        zipLists ~expected:paramTypes ~actual:args ~makeError:(fun ea ->
            { source = argsSource; elem = WrongNumberOfArguments ea })
      in
      let eqShapeElement =
        Typed.Index.(
          function
          | ShapeRef a, ShapeRef b -> Typed.Identifier.equal a b
          | Add a, Add b -> a.const = b.const && Map.equal ( = ) a.refs b.refs
          | ShapeRef _, Add _ | Add _, ShapeRef _ -> false)
      in
      let%bind frames =
        zippedArgs
        |> List.map ~f:(fun (param, (_, argType, argSource)) ->
               (* Check the element type is correct *)
               let checkElementType =
                 requireType
                   ~expected:(Typed.Type.Atom param.element)
                   ~actual:(Typed.Type.Atom argType.element)
                   ~makeError:(fun ea ->
                     { source = argSource; elem = ArgumentTypeDisagreement ea })
               in
               (* Check that the cell shape is correct and get the frame *)
               let checkCellAndGetFrame =
                 let frame, argCell =
                   List.split_n
                     argType.shape
                     (List.length argType.shape - List.length param.shape)
                 in
                 let cellDisagreementErr =
                   { source = argSource
                   ; elem =
                       CellShapeDisagreement
                         { expected = param.shape; actual = argType.shape }
                   }
                 in
                 let%bind zippedCellElements =
                   zipLists ~expected:param.shape ~actual:argCell ~makeError:(fun _ ->
                       cellDisagreementErr)
                 in
                 let allShapeElementsAgree =
                   List.for_all zippedCellElements ~f:eqShapeElement
                 in
                 let%map () =
                   CheckerStateT.require allShapeElementsAgree cellDisagreementErr
                 in
                 frame
               in
               let%map () = checkElementType
               and frame = checkCellAndGetFrame in
               { elem = frame; source = argSource })
        |> CheckerStateT.all
      in
      let getPrincipalFrame
          (headFrame :: restFrames : ('s, Typed.Index.shape) Source.annotate NeList.t)
        =
        (* Get the principal frame *)
        let principalFrame, _ =
          List.fold
            restFrames
            ~init:(headFrame.elem, List.length headFrame.elem)
            ~f:(fun (maxFrame, maxSize) { elem = curr; source = _ } ->
              let currSize = List.length curr in
              if currSize > maxSize then curr, currSize else maxFrame, maxSize)
        in
        (* Check that each frame conforms to the principal frame *)
        let%map () =
          headFrame :: restFrames
          |> List.map ~f:(fun { elem = frame; source = frameSource } ->
                 let rec zipAndDropRemainder a b =
                   match a, b with
                   | a :: aRest, b :: bRest -> (a, b) :: zipAndDropRemainder aRest bRest
                   | _, [] | [], _ -> []
                 in
                 let zippedShapeElements = zipAndDropRemainder principalFrame frame in
                 let allShapeElementsAgree =
                   List.for_all zippedShapeElements ~f:eqShapeElement
                 in
                 CheckerStateT.require
                   allShapeElementsAgree
                   { source = frameSource
                   ; elem =
                       PrincipalFrameDisagreement
                         { expected = principalFrame; actual = frame }
                   })
          |> CheckerStateT.all_unit
        in
        principalFrame
      in
      let%map principalFrame =
        getPrincipalFrame ({ elem = funcShape; source = funcSource } :: frames)
      in
      T.Array
        (T.TermApplication
           { func
           ; args = List.map args ~f:(fun (arg, _, _) -> arg)
           ; type' =
               { element = returnType.element; shape = principalFrame @ returnType.shape }
           })
    | U.TypeApplication { tFunc; args } ->
      let%bind tFuncTyped = checkAndExpectArray env tFunc in
      let%bind tFuncType = checkForArrType tFunc.source (T.arrayType tFuncTyped) in
      let%bind tFuncForall =
        match tFuncType.element with
        | Typed.Type.Forall forall -> ok forall
        | _ as t ->
          CheckerStateT.err
            { source = tFunc.source
            ; elem = ExpectedForall { actual = Typed.Type.Atom t }
            }
      in
      let%bind bodyType = checkForArrType tFunc.source tFuncForall.body in
      let%bind zippedArgs =
        zipLists ~expected:args.elem ~actual:tFuncForall.parameters ~makeError:(fun ea ->
            { source = args.source; elem = WrongNumberOfArguments ea })
      in
      let%map substitutionsList =
        zippedArgs
        |> List.map ~f:(fun (arg, param) ->
               let%map typedArg = KindChecker.checkAndExpect param.bound env arg in
               param.binding, typedArg)
        |> CheckerStateT.all
      in
      let substitutions =
        Map.of_alist_reduce (module Typed.Identifier) substitutionsList ~f:(fun a _ -> a)
      in
      let subbedElementType = subTypesIntoAtomType substitutions bodyType.element in
      let typedArgs = List.map substitutionsList ~f:(fun (_, arg) -> arg) in
      T.Array
        (T.TypeApplication
           { tFunc = tFuncTyped
           ; args = typedArgs
           ; type' =
               { element = subbedElementType; shape = tFuncType.shape @ bodyType.shape }
           })
    | U.IndexApplication { iFunc; args } ->
      let%bind iFuncTyped = checkAndExpectArray env iFunc in
      let%bind iFuncType = checkForArrType iFunc.source (T.arrayType iFuncTyped) in
      let%bind iFuncPi =
        match iFuncType.element with
        | Typed.Type.Pi pi -> ok pi
        | _ as t ->
          CheckerStateT.err
            { source = iFunc.source
            ; elem = ExpectedForall { actual = Typed.Type.Atom t }
            }
      in
      let%bind bodyType = checkForArrType iFunc.source iFuncPi.body in
      let%bind zippedArgs =
        zipLists ~expected:iFuncPi.parameters ~actual:args.elem ~makeError:(fun ea ->
            { source = args.source; elem = WrongNumberOfArguments ea })
      in
      let%map substitutionsList =
        zippedArgs
        |> List.map ~f:(fun (param, arg) ->
               let%map typedArg = SortChecker.checkAndExpect param.bound env arg in
               param.binding, typedArg)
        |> CheckerStateT.all
      in
      let substitutions =
        Map.of_alist_reduce (module Typed.Identifier) substitutionsList ~f:(fun a _ -> a)
      in
      let subbedElementType = subIndicesIntoAtomType substitutions bodyType.element in
      let subbedBodyShape = subIndicesIntoShapeIndex substitutions bodyType.shape in
      let typedArgs = List.map substitutionsList ~f:(fun (_, arg) -> arg) in
      T.Array
        (T.IndexApplication
           { iFunc = iFuncTyped
           ; args = typedArgs
           ; type' =
               { element = subbedElementType; shape = iFuncType.shape @ subbedBodyShape }
           })
    | U.Unbox { indexBindings; valueBinding; box; body } ->
      let boxSource = box.source in
      let%bind box = checkAndExpectArray env box in
      let%bind boxArrType = checkForArrType boxSource (T.arrayType box) in
      let%bind sigma = checkForSigmaType boxSource boxArrType.element in
      let%bind zippedIndexBindings =
        zipLists
          ~expected:sigma.parameters
          ~actual:indexBindings.elem
          ~makeError:(fun ea ->
            { source = indexBindings.source; elem = WrongNumberOfUnboxParameters ea })
      in
      let%bind indexBindingsRev, newSortEnvEntries, substitutions =
        List.fold
          zippedIndexBindings
          ~init:(ok ([], Map.empty (module String), Map.empty (module Typed.Identifier)))
          ~f:(fun soFar (param, binding) ->
            let%bind bindingsSoFar, entriesSoFar, subsSoFar = soFar in
            let%bind () =
              match binding.elem.bound with
              | Some bound ->
                if Sort.equal bound.elem param.bound
                then ok ()
                else
                  CheckerStateT.err
                    { source = bound.source
                    ; elem =
                        UnexpectedSortBoundInUnbox
                          { expected = param.bound; actual = bound.elem }
                    }
              | None -> ok ()
            in
            let%bind id = CheckerStateT.createId binding.elem.binding.elem in
            let%map entries =
              match
                Map.add
                  entriesSoFar
                  ~key:binding.elem.binding.elem
                  ~data:Environment.{ e = param.bound; id }
              with
              | `Ok entries -> ok entries
              | `Duplicate ->
                CheckerStateT.err
                  { source = binding.elem.binding.source
                  ; elem = DuplicateParameterName binding.elem.binding.elem
                  }
            in
            let indexRef =
              match param.bound with
              | Sort.Dim -> Typed.Index.Dimension (Typed.Index.dimensionRef id)
              | Sort.Shape -> Typed.Index.Shape [ Typed.Index.ShapeRef id ]
            in
            let subs = Map.set subsSoFar ~key:param.binding ~data:indexRef in
            let bindings = id :: bindingsSoFar in
            bindings, entries, subs)
      in
      let%bind () =
        CheckerStateT.require
          (Option.is_none (Map.find newSortEnvEntries valueBinding.elem))
          { source = valueBinding.source
          ; elem = DuplicateParameterName valueBinding.elem
          }
      in
      let extendedSorts =
        Map.merge_skewed env.sorts newSortEnvEntries ~combine:(fun ~key:_ _ newEntry ->
            newEntry)
      in
      let%bind valueBindingTyped = CheckerStateT.createId valueBinding.elem in
      let extendedTypes =
        Map.set
          env.types
          ~key:valueBinding.elem
          ~data:
            { e = subIndicesIntoArrayType substitutions sigma.body
            ; id = valueBindingTyped
            }
      in
      let extendedEnv = { env with sorts = extendedSorts; types = extendedTypes } in
      let bodySource = body.source in
      let%bind body = checkAndExpectArray extendedEnv body in
      let%bind bodyType = checkForArrType bodySource (T.arrayType body) in
      let%map () =
        match findEscapingRefs env (Typed.Type.Array (Typed.Type.Arr bodyType)) with
        | [] -> ok ()
        | ref :: _ ->
          CheckerStateT.err { source = bodySource; elem = EscapingRef ref.name }
      in
      T.Array
        (T.Unbox
           { indexBindings = List.rev indexBindingsRev
           ; valueBinding = valueBindingTyped
           ; box
           ; body
           ; type' =
               { element = bodyType.element; shape = boxArrType.shape @ bodyType.shape }
           })
    | U.TermLambda { params; body } ->
      let%bind kindedParams =
        params.elem
        |> List.map ~f:(fun { elem = { binding; bound }; source } ->
               let%map bound = KindChecker.checkAndExpectArray env bound in
               let param : ('s, Typed.Type.array) Untyped.param = { binding; bound } in
               { elem = param; source })
        |> CheckerStateT.all
      in
      let%bind { typedParams; extendedEnv = extendedTypesEnv } =
        processParams
          env.types
          kindedParams
          ~makeError:(fun name -> DuplicateParameterName name)
          ~boundToEnvEntry:(fun b -> b)
      in
      let extendedEnv = { env with types = extendedTypesEnv } in
      let%map body = checkAndExpectArray extendedEnv body in
      let type' : Typed.Type.func =
        { parameters = List.map typedParams ~f:(fun p -> p.bound)
        ; return = T.arrayType body
        }
      in
      T.Atom (T.TermLambda { params = typedParams; body = T.Array body; type' })
    | U.TypeLambda { params; body } ->
      let params =
        (* The parameter's have source-annotated bounds; remove the source annotations *)
        List.map params.elem ~f:(function
            | { elem = { binding; bound = { elem = bound; source = _ } }; source } ->
            { elem = ({ binding; bound } : ('s, Kind.t) Untyped.param); source })
      in
      let%bind { typedParams; extendedEnv = extendedKindsEnv } =
        processParams
          env.kinds
          params
          ~makeError:(fun name -> DuplicateParameterName name)
          ~boundToEnvEntry:(fun b -> b)
      in
      let extendedEnv = { env with kinds = extendedKindsEnv } in
      let%bind () = requireValue body in
      let%map body = checkAndExpectArray extendedEnv body in
      let type' : Typed.Type.forall =
        { parameters = typedParams; body = T.arrayType body }
      in
      T.Atom (T.TypeLambda { params = typedParams; body; type' })
    | U.IndexLambda { params; body } ->
      let params =
        (* The parameter's have source-annotated bounds; remove the source annotations *)
        List.map params.elem ~f:(function
            | { elem = { binding; bound = { elem = bound; source = _ } }; source } ->
            { elem = ({ binding; bound } : ('s, Sort.t) Untyped.param); source })
      in
      let%bind { typedParams; extendedEnv = extendedSortsEnv } =
        processParams
          env.sorts
          params
          ~makeError:(fun name -> DuplicateParameterName name)
          ~boundToEnvEntry:(fun b -> b)
      in
      let extendedEnv = { env with sorts = extendedSortsEnv } in
      let%bind () = requireValue body in
      let%map body = checkAndExpectArray extendedEnv body in
      let type' : Typed.Type.pi = { parameters = typedParams; body = T.arrayType body } in
      T.Atom (T.IndexLambda { params = typedParams; body; type' })
    | U.Boxes { params; elementType; dimensions; elements } ->
      let%bind typedParams =
        params.elem
        |> List.map ~f:(fun p ->
               let%map id = CheckerStateT.createId p.elem.binding.elem in
               let typedParam : Sort.t Typed.param =
                 { binding = id; bound = p.elem.bound.elem }
               in
               typedParam)
        |> CheckerStateT.all
      in
      let dimensions = List.map dimensions.elem ~f:(fun d -> d.elem) in
      let expectedElements = List.fold dimensions ~init:1 ~f:( * ) in
      let%bind elementType = KindChecker.checkAndExpectArray env elementType
      and checkedElements =
        elements.elem
        |> List.map ~f:(fun e ->
               let%map indices =
                 e.elem.indices.elem
                 |> List.map ~f:(fun index ->
                        SortChecker.check env index >>| fun i -> i, index.source)
                 |> CheckerStateT.all
               and body = checkAndExpectArray env e.elem.body in
               indices, body, e)
        |> CheckerStateT.all
      and _ =
        CheckerStateT.require
          (List.length elements.elem = expectedElements)
          { elem =
              WrongNumberOfElementsInBoxes
                { expected = expectedElements; actual = List.length elements.elem }
          ; source = elements.source
          }
      in
      let%map boxes =
        checkedElements
        |> List.map ~f:(fun (indices, body, element) ->
               let%bind zippedIndices =
                 zipLists ~expected:typedParams ~actual:indices ~makeError:(fun ea ->
                     { source = element.elem.indices.source
                     ; elem = WrongNumberOfArguments ea
                     })
               in
               let%bind substitutions =
                 List.fold
                   zippedIndices
                   ~init:(ok (Map.empty (module Typed.Identifier)))
                   ~f:(fun acc _ -> acc)
               in
               let subbedType = subIndicesIntoArrayType substitutions elementType in
               let%map () =
                 requireType
                   ~expected:(Typed.Type.Array subbedType)
                   ~actual:(T.type' (T.Array body))
                   ~makeError:(fun ea ->
                     { source = element.elem.body.source
                     ; elem = SigmaBodyTypeDisagreement ea
                     })
               in
               ({ indices = List.map indices ~f:(fun (i, _) -> i)
                ; body
                ; bodyType = elementType
                ; type' = { parameters = typedParams; body = elementType }
                }
                 : T.box))
        |> CheckerStateT.all
      in
      let shape =
        List.map dimensions ~f:(fun d ->
            Typed.Index.Add (Typed.Index.dimensionConstant d))
      in
      let sigmaType : Typed.Type.sigma =
        { parameters = typedParams; body = elementType }
      in
      T.Array
        (T.Arr
           { dimensions
           ; elements = List.map boxes ~f:(fun b -> T.Box b)
           ; type' = { element = Typed.Type.Sigma sigmaType; shape }
           })
    | U.Let { param; value; body } ->
      let binding = param.elem.binding in
      let bound = param.elem.bound in
      let%bind id = CheckerStateT.createId binding.elem in
      let%bind bound =
        bound
        |> Option.map ~f:(fun bound -> KindChecker.checkAndExpectArray env bound)
        |> CheckerStateT.traverseOpt
      in
      let checkBody valueType =
        let extendedTypesEnv =
          Map.set env.types ~key:binding.elem ~data:{ id; e = valueType }
        in
        let extendedEnv = { env with types = extendedTypesEnv } in
        checkAndExpectArray extendedEnv body
      in
      let checkValue =
        let%bind valueTyped = checkAndExpectArray env value in
        let%map () =
          match bound with
          | Some bound ->
            requireType
              ~expected:(Array bound)
              ~actual:(T.type' (Array valueTyped))
              ~makeError:(fun ea ->
                { source = value.source; elem = LetTypeDisagreement ea })
          | None -> ok ()
        in
        valueTyped
      in
      let%map bodyTyped, valueTyped =
        match bound with
        | Some bound -> CheckerStateT.both (checkBody bound) checkValue
        | None ->
          let%bind valueTyped = checkValue in
          let%map bodyTyped = checkBody (T.arrayType valueTyped) in
          bodyTyped, valueTyped
      in
      T.Array
        (T.Let
           { binding = id
           ; value = valueTyped
           ; body = bodyTyped
           ; type' = T.arrayType bodyTyped
           })
    | U.TupleLet { params; value; body } ->
      let%bind valueTyped = checkAndExpectArray env value in
      let%bind valueType = checkForArrType value.source (T.arrayType valueTyped) in
      let%bind valueElementType = checkForTupleType value.source valueType.element in
      let%bind zippedBindings =
        zipLists ~expected:valueElementType ~actual:params.elem ~makeError:(fun ea ->
            { source = params.source; elem = WrongNumberOfBindings ea })
      in
      let%bind newEnvEntries, revParamsTyped =
        List.fold
          zippedBindings
          ~init:(ok (Map.empty (module String), []))
          ~f:(fun acc (type', param) ->
            let%bind envEntriesSoFar, paramsSoFar = acc in
            let%bind id = CheckerStateT.createId param.elem.binding.elem in
            let%bind boundTyped =
              match param.elem.bound with
              | Some bound ->
                let%bind boundTyped = KindChecker.checkAndExpectAtom env bound in
                let%map () =
                  requireType
                    ~expected:(Atom type')
                    ~actual:(Atom boundTyped)
                    ~makeError:(fun ea ->
                      { source = bound.source; elem = TupleLetTypeDisagreement ea })
                in
                boundTyped
              | None -> ok type'
            in
            let bindingType =
              Typed.Type.Arr { element = boundTyped; shape = valueType.shape }
            in
            let entry = Environment.{ id; e = bindingType } in
            let paramTyped = Typed.{ binding = id; bound = boundTyped } in
            match Map.add envEntriesSoFar ~key:param.elem.binding.elem ~data:entry with
            | `Ok envEntries -> ok (envEntries, paramTyped :: paramsSoFar)
            | `Duplicate ->
              CheckerStateT.err
                { source = param.elem.binding.source
                ; elem = DuplicateTupleBindingName param.elem.binding.elem
                })
      in
      let extendedTypesEnv =
        Map.merge_skewed env.types newEnvEntries ~combine:(fun ~key:_ _ e -> e)
      in
      let extendedEnv = { env with types = extendedTypesEnv } in
      let%map bodyTyped = checkAndExpectArray extendedEnv body in
      T.Array
        (TupleLet
           { params = List.rev revParamsTyped
           ; value = valueTyped
           ; body = bodyTyped
           ; type' = T.arrayType bodyTyped
           })
    | U.Tuple elements ->
      let%map elements =
        elements.elem |> List.map ~f:(checkAndExpectAtom env) |> CheckerStateT.all
      in
      let elementTypes = List.map elements ~f:(fun e -> T.atomType e) in
      T.Atom (T.Tuple { elements; type' = elementTypes })
    | U.IntLiteral i -> CheckerStateT.return (T.Atom (T.IntLiteral i))
    | U.CharacterLiteral i -> CheckerStateT.return (T.Atom (T.CharacterLiteral i))

  and checkAndExpectArray env expr =
    let open Typed.Expr in
    match%bind check env expr with
    | Array array -> ok array
    | Atom atom ->
      ok
        (Typed.Expr.Arr
           { dimensions = []
           ; elements = [ atom ]
           ; type' = { element = Typed.Expr.atomType atom; shape = [] }
           })

  and checkAndExpectAtom env expr =
    let open Typed.Expr in
    match%bind check env expr with
    | Atom atom -> ok atom
    | Array _ as typed ->
      CheckerStateT.err
        { source = expr.source; elem = ExpectedAtomicExpr { actual = type' typed } }
  ;;
end

let baseEnv () =
  let module B = Environment.Base (CheckerStateT) in
  B.make ()
;;

let checkSort index =
  CheckerStateT.runA
    (let%bind env = baseEnv () in
     SortChecker.check env index)
    { idCounter = 0 }
;;

let checkKind type' =
  CheckerStateT.runA
    (let%bind env = baseEnv () in
     KindChecker.check env type')
    { idCounter = 0 }
;;

let checkType expr =
  CheckerStateT.runA
    (let%bind env = baseEnv () in
     TypeChecker.check env expr)
    { idCounter = 0 }
;;
