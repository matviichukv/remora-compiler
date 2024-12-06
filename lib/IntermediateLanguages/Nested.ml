open! Base

(* The Nested language represents a Remora program where maps only operate
   on one shape element at a time and can be fused with consumers *)

module Index = struct
  include Nucleus.Index

  let sexp_of_dimension ({ const; refs } : dimension) =
    match Map.to_alist refs with
    | [] -> Sexp.Atom (Int.to_string const)
    | [ (ref, 1) ] when const = 0 -> Sexp.Atom (Identifier.show ref)
    | refs ->
      Sexp.List
        ([ Sexp.Atom "+"; Sexp.Atom (Int.to_string const) ]
         @ List.bind refs ~f:(fun (ref, count) ->
           let refSexp = Sexp.Atom (Identifier.show ref) in
           List.init count ~f:(fun _ -> refSexp)))
  ;;

  let sexp_of_shapeElement = function
    | Nucleus.Index.Add dimension -> sexp_of_dimension dimension
    | Nucleus.Index.ShapeRef ref -> Sexp.Atom (Identifier.show ref)
  ;;

  let sexp_of_shape shape =
    Sexp.List (Sexp.Atom "shape" :: List.map shape ~f:sexp_of_shapeElement)
  ;;

  let sexp_of_t = function
    | Nucleus.Index.Shape shape -> sexp_of_shape shape
    | Nucleus.Index.Dimension dimension -> sexp_of_dimension dimension
  ;;
end

module Type = struct
  type array =
    { element : t
    ; size : Index.shapeElement
    }

  and sigmaParam = Nucleus.Type.sigmaParam

  and sigma =
    { parameters : sigmaParam list
    ; body : t
    }

  and tuple = t list
  and literal = Nucleus.Type.literal

  and t =
    | Array of array
    | Sigma of sigma
    | Literal of literal
    | Tuple of tuple
  [@@deriving sexp_of, equal, compare]
end

module Expr = struct
  type indexMode =
    { allocatedThreads : int option
    ; allocatedBlocks : int option
    }
  [@@deriving sexp_of, equal, compare]

  type ref =
    { id : Identifier.t
    ; type' : Type.t
    }

  and reduceCharacter = Nucleus.Expr.reduceCharacter
  and foldCharacter = Nucleus.Expr.foldCharacter

  and frame =
    { dimension : int
    ; elements : t list
    ; type' : Type.t
    }

  and boxValue =
    { box : t
    ; type' : Type.t
    }

  and indexValue =
    | Runtime of t
    | FromBox of
        { box : t
        ; i : int
        }

  and indexArg =
    { indexBinding : Identifier.t
    ; indexValue : indexValue
    ; sort : Sort.t
    }

  and indexLet =
    { indexArgs : indexArg list
    ; body : t
    ; type' : Type.t
    }

  and reifyIndex =
    { index : Index.t
    ; type' : Type.t
    }

  and letArg =
    { binding : Identifier.t
    ; value : t
    }

  and let' =
    { args : letArg list
    ; body : t
    ; type' : Type.t
    }

  and box =
    { indices : Index.t list
    ; body : t
    ; bodyType : Type.t
    ; type' : Type.sigma
    }

  and scalarOp =
    | Add
    | Sub
    | Mul
    | Div
    | Mod
    | AddF
    | SubF
    | MulF
    | DivF
    | IntToBool
    | BoolToInt
    | IntToFloat
    | FloatToInt
    | Equal
    | EqualF
    | Ne
    | Gt
    | GtEq
    | Lt
    | LtEq
    | GtF
    | GtEqF
    | LtF
    | LtEqF
    | And
    | Or
    | Not
    | If
    | LibFun of
        { name : string
        ; libName : string
        ; argTypes : Type.t list
        ; retType : Type.t
        }
    | IOFun of
        { name : string
        ; libName : string
        ; libTypeParams : Type.t list
        ; argTypes : Type.t list
        ; retType : Type.t
        }

  and scalarPrimitive =
    { op : scalarOp
    ; args : t list
    ; type' : Type.t
    }

  and tupleMatch =
    | Binding of Identifier.t
    | Unpack of tupleMatch list

  and mapArg =
    { binding : Identifier.t
    ; ref : ref
    }
  [@@deriving compare]

  and loopBlock =
    { label : Identifier.t
    ; frameShape : Index.shapeElement
    ; mapArgs : mapArg list
    ; mapIotas : Identifier.t list
    ; mapBody : t
    ; mapBodyMatcher : tupleMatch
    ; mapResults : Identifier.t list
    ; consumer : consumerOp option
    ; type' : Type.tuple
    }
  (* loop block with labels and optional indexing *)

  (* and loopBlock =
    { frameShape : Index.shapeElement
    ; mapArgs : mapArg list
    ; mapIotas : Identifier.t list
    ; mapBody : t
    ; mapBodyMatcher : tupleMatch
    ; mapResults : Identifier.t list
    ; consumer : consumerOp option
    ; type' : Type.tuple
    ; label : Identifier.t
    ; indexingModeMap : indexMode option
    } *)

  (** returns a tuple of (map results (tuple of arrays, not array of tuples), consumer result (unit if None)) *)

  and foldZeroArg =
    { zeroBinding : Identifier.t
    ; zeroValue : t
    }

  and production =
    { productionId : Identifier.t
    ; type' : Type.t
    }

  and foldArrayArg =
    { binding : Identifier.t
    ; production : production
    }

  and productionTuple =
    | ProductionTuple of
        { elements : productionTuple list
        ; type' : Type.t
        }
    | ProductionTupleAtom of production

  and reduceArg =
    { firstBinding : Identifier.t
    ; secondBinding : Identifier.t
    ; production : productionTuple
    }

  and consumerOp =
    | Reduce of
        { arg : reduceArg
        ; zero : t
        ; body : t
        ; d : Index.dimension
        ; character : reduceCharacter
        ; type' : Type.t
        }
    | Fold of
        { zeroArg : foldZeroArg
        ; arrayArgs : foldArrayArg list
        ; body : t
        ; reverse : bool
        ; d : Index.dimension
        ; character : foldCharacter
        ; type' : Type.t
        }
    | Scatter of
        { valuesArg : production
        ; indicesArg : production
        ; dIn : Index.dimension
        ; dOut : Index.dimension
        ; type' : Type.t
        }

  and tuple =
    { elements : t list
    ; type' : Type.tuple
    }

  and tupleDeref =
    { index : int
    ; tuple : t
    ; type' : Type.t
    }

  and literal = Nucleus.Expr.literal

  and contiguousSubArray =
    { arrayArg : t
    ; indexArg : t
    ; originalShape : Index.shape
    ; resultShape : Index.shape
    ; type' : Type.t
    }

  and append =
    { args : t list
    ; type' : Type.t
    }

  (** Zip collections together, going `nestCount` deep. A "collection" is
      a box or array. The arg is expected to be a tuple *)
  and zip =
    { zipArg : t
    ; nestCount : int
    ; type' : Type.t
    }

  (** Unzip nested collections, recursively entering collections until a tuple
      is reached *)
  and unzip =
    { unzipArg : t
    ; type' : Type.tuple
    }

  and t =
    | Ref of ref
    | Frame of frame
    | BoxValue of boxValue
    | IndexLet of indexLet
    | ReifyIndex of reifyIndex
    | ShapeProd of Index.shape
    | Let of let'
    | LoopBlock of loopBlock
    | Box of box
    | Literal of literal
    | Tuple of tuple
    | ScalarPrimitive of scalarPrimitive
    | TupleDeref of tupleDeref
    | ContiguousSubArray of contiguousSubArray
    | Append of append
    | Zip of zip
    | Unzip of unzip
  [@@deriving equal, compare]

  let type' : t -> Type.t = function
    | Box box -> Sigma box.type'
    | Literal (IntLiteral _) -> Literal (IntLiteral Int32)
    | Literal (FloatLiteral _) -> Literal FloatLiteral
    | Literal (CharacterLiteral _) -> Literal CharacterLiteral
    | Literal (BooleanLiteral _) -> Literal BooleanLiteral
    | Literal (StringLiteral _) -> Literal StringLiteral
    | ScalarPrimitive scalarPrimitive -> scalarPrimitive.type'
    | TupleDeref tupleDeref -> tupleDeref.type'
    | Tuple tuple -> Tuple tuple.type'
    | Ref ref -> ref.type'
    | Frame frame -> frame.type'
    | BoxValue boxValue -> boxValue.type'
    | IndexLet indexLet -> indexLet.type'
    | Let let' -> let'.type'
    | ReifyIndex reifyIndex -> reifyIndex.type'
    | ShapeProd _ -> Literal (IntLiteral Int32)
    | LoopBlock loopBlock -> Tuple loopBlock.type'
    | ContiguousSubArray contiguousSubArray -> contiguousSubArray.type'
    | Append append -> append.type'
    | Zip zip -> zip.type'
    | Unzip unzip -> Tuple unzip.type'
  ;;

  let consumerOpType = function
    | Reduce reduce -> reduce.type'
    | Fold fold -> fold.type'
    | Scatter scatter -> scatter.type'
  ;;

  let productionTupleType = function
    | ProductionTuple productionTuple -> productionTuple.type'
    | ProductionTupleAtom productionTupleAtom -> productionTupleAtom.type'
  ;;

  let tuple elements = Tuple { elements; type' = List.map elements ~f:type' }
  let let' ~args ~body = Let { args; body; type' = type' body }

  let ( + ) a b =
    ScalarPrimitive { op = Add; args = [ a; b ]; type' = Literal (IntLiteral Int32) }
  ;;

  let ( * ) a b =
    ScalarPrimitive { op = Mul; args = [ a; b ]; type' = Literal (IntLiteral Int32) }
  ;;

  let tupleDeref ~tuple ~index =
    TupleDeref
      { tuple
      ; index
      ; type' =
          (match type' tuple with
           | Tuple types -> List.nth_exn types index
           | _ -> raise (Unreachable.Error "Expected tuple type"))
      }
  ;;

  let unzip unzipArg =
    let rec unzipType type' =
      match type' with
      | Type.Array { element; size } ->
        unzipType element |> List.map ~f:(fun e -> Type.Array { element = e; size })
      | Type.Sigma { parameters; body } ->
        unzipType body |> List.map ~f:(fun e -> Type.Sigma { parameters; body = e })
      | Type.Tuple t -> t
      | Type.Literal _ -> raise (Unreachable.Error "Expected collection or tuple type")
    in
    Unzip { unzipArg; type' = unzipType @@ type' unzipArg }
  ;;

  module Sexp_of = struct
    let sexp_of_ref ref = Sexp.Atom (Identifier.show ref.id)
    (* Sexp.List [ Sexp.Atom (Identifier.show ref.id); Type.sexp_of_t ref.type' ] *)

    let rec sexp_of_frame { dimension = _; elements; type' = _ } =
      Sexp.List (Sexp.Atom "frame" :: List.map elements ~f:sexp_of_t)

    and sexp_of_box { indices; body; bodyType = _; type' = _ } =
      Sexp.List
        [ Sexp.Atom "box"
        ; Sexp.List (List.map indices ~f:Index.sexp_of_t)
        ; sexp_of_t body
        ]

    and sexp_of_literal (lit : Nucleus.Expr.literal) =
      match lit with
      | IntLiteral i -> Sexp.Atom (Int.to_string i)
      | FloatLiteral f -> Sexp.Atom (Float.to_string f)
      | CharacterLiteral c -> Sexp.Atom [%string "'%{Char.to_string c}'"]
      | BooleanLiteral b -> Sexp.Atom (if b then "true" else "false")
      | StringLiteral s -> Sexp.Atom s

    and sexp_of_scalarOp (op : scalarOp) =
      Sexp.Atom
        (match op with
         | Add -> "+"
         | Sub -> "-"
         | Mul -> "*"
         | Div -> "/"
         | Mod -> "%"
         | AddF -> "+."
         | SubF -> "-."
         | MulF -> "*."
         | DivF -> "/."
         | And -> "and"
         | Or -> "or"
         | Not -> "not"
         | If -> "if"
         | IntToBool -> "int->bool"
         | BoolToInt -> "bool->int"
         | IntToFloat -> "int->float"
         | FloatToInt -> "float->int"
         | Equal -> "="
         | EqualF -> "=."
         | Ne -> "!="
         | Gt -> ">"
         | GtEq -> ">="
         | Lt -> "<"
         | LtEq -> "<="
         | GtF -> ">."
         | GtEqF -> ">=."
         | LtF -> "<."
         | LtEqF -> "<=."
         | LibFun { name; libName = _; argTypes = _; retType = _ } -> name
         | IOFun { name; libName = _; libTypeParams = _; argTypes = _; retType = _ } ->
           name)

    and sexp_of_scalarPrimitive { op; args; type' = _ } =
      Sexp.List (sexp_of_scalarOp op :: List.map args ~f:sexp_of_t)

    and sexp_of_tupleDeref { tuple; index; type' = _ } =
      Sexp.List [ Sexp.Atom [%string "#%{index#Int}"]; sexp_of_t tuple ]

    and sexp_of_tuple ({ elements; type' = _ } : tuple) =
      Sexp.List
        (Sexp.Atom "tuple" (* :: List.sexp_of_t Type.sexp_of_t type' *)
         :: List.map elements ~f:sexp_of_t)

    and sexp_of_boxValue { box; type' = _ } =
      Sexp.List [ Sexp.Atom "unbox"; sexp_of_t box ]

    and sexp_of_indexLet { indexArgs; body; type' = _ } =
      Sexp.List
        [ Sexp.Atom "index-let"
        ; Sexp.List
            (List.map indexArgs ~f:(fun { indexBinding; indexValue; sort = _ } ->
               Sexp.List
                 (Sexp.Atom (Identifier.show indexBinding)
                  ::
                  (match indexValue with
                   | Runtime v -> [ Sexp.Atom "runtime-value"; sexp_of_t v ]
                   | FromBox { box; i } ->
                     [ Sexp.Atom [%string "box-index-%{i#Int}"]; sexp_of_t box ]))))
        ; sexp_of_t body
        ]

    and sexp_of_letArg { binding; value } =
      Sexp.List
        [ Sexp.Atom (Identifier.show binding) (* ; Type.sexp_of_t (type' value) *)
        ; sexp_of_t value
        ]

    and sexp_of_let { args; body; type' = _ } =
      Sexp.List
        [ Sexp.Atom "let"
        ; Sexp.List (List.map args ~f:sexp_of_letArg) (* ; Type.sexp_of_t type' *)
        ; sexp_of_t body
        ]

    and sexp_of_reifyIndex { index; type' = _ } =
      Sexp.List [ Sexp.Atom "reify-index"; Index.sexp_of_t index ]

    and sexp_of_tupleMatch = function
      | Binding id -> Sexp.Atom (Identifier.show id)
      | Unpack matchers -> Sexp.List (List.map matchers ~f:sexp_of_tupleMatch)

    and sexp_of_productionTuple = function
      | ProductionTuple { elements; type' = _ } ->
        Sexp.List (List.map elements ~f:sexp_of_productionTuple)
      | ProductionTupleAtom p -> Sexp.Atom (Identifier.show p.productionId)

    and sexp_of_consumerOp = function
      | Reduce { arg; zero; body; d = _; character; type' = _ } ->
        let characterName =
          match character with
          | Reduce -> "reduce"
          | Scan -> "scan"
        in
        let opName = [%string "%{characterName}-zero"] in
        Sexp.List
          [ Sexp.Atom opName
          ; sexp_of_t zero
          ; Sexp.List
              [ Sexp.Atom (Identifier.show arg.firstBinding)
              ; Sexp.Atom (Identifier.show arg.secondBinding)
              ; sexp_of_productionTuple arg.production
              ]
          ; sexp_of_t body
          ]
      | Fold { zeroArg; arrayArgs; body; reverse; d = _; character; type' = _ } ->
        let opName =
          match reverse, character with
          | false, Fold -> "fold"
          | true, Fold -> "fold-right"
          | false, Trace -> "trace"
          | true, Trace -> "trace-right"
        in
        Sexp.List
          [ Sexp.Atom opName
          ; Sexp.List
              [ Sexp.Atom (Identifier.show zeroArg.zeroBinding)
              ; sexp_of_t zeroArg.zeroValue
              ]
          ; Sexp.List
              (List.map arrayArgs ~f:(fun arrayArg ->
                 Sexp.List
                   [ Sexp.Atom (Identifier.show arrayArg.binding)
                   ; Sexp.Atom (Identifier.show arrayArg.production.productionId)
                   ]))
          ; sexp_of_t body
          ]
      | Scatter { valuesArg; indicesArg; dIn; dOut; type' = _ } ->
        Sexp.List
          [ Sexp.Atom "scatter"
          ; Index.sexp_of_dimension dIn
          ; Index.sexp_of_dimension dOut
          ; Sexp.Atom (Identifier.show valuesArg.productionId)
          ; Sexp.Atom (Identifier.show indicesArg.productionId)
          ]

    and sexp_of_mapArg { binding; ref } =
      Sexp.List
        [ Sexp.Atom (Identifier.show binding); Sexp.Atom (Identifier.show ref.id) ]

    and sexp_of_loopBlock
      { frameShape
      ; mapArgs
      ; mapIotas
      ; mapBody
      ; mapBodyMatcher
      ; mapResults
      ; consumer
      ; label
      ; type' = _
      }
      =
      Sexp.List
        [ Sexp.Atom "loop-block"
        ; [%sexp_of: Identifier.t] label
        ; Sexp.List [ Sexp.Atom "frame-shape"; Index.sexp_of_shapeElement frameShape ]
        ; Sexp.List
            ([ Sexp.Atom "map"; Sexp.List (List.map mapArgs ~f:sexp_of_mapArg) ]
             @ (if List.length mapIotas > 0
                then
                  [ Sexp.List
                      (Sexp.Atom "iota" :: List.map mapIotas ~f:[%sexp_of: Identifier.t])
                  ]
                else [])
             @ [ sexp_of_t mapBody ])
        ; Sexp.List [ Sexp.Atom "body-matcher"; sexp_of_tupleMatch mapBodyMatcher ]
        ; Sexp.List
            [ Sexp.Atom "map-result"
            ; Sexp.List
                (List.map mapResults ~f:(fun id -> Sexp.Atom (Identifier.show id)))
            ]
        ; Sexp.List
            [ Sexp.Atom "consumer"
            ; (match consumer with
               | Some consumer -> sexp_of_consumerOp consumer
               | None -> sexp_of_tuple { elements = []; type' = [] })
            ]
        ]

    and sexp_of_contiguousSubArray
      { arrayArg; indexArg; originalShape; resultShape; type' = _ }
      =
      Sexp.List
        [ Sexp.Atom "contiguous-subarray"
        ; sexp_of_t arrayArg
        ; sexp_of_t indexArg
        ; [%sexp_of: Index.shape] originalShape
        ; [%sexp_of: Index.shape] resultShape
        ]

    and sexp_of_append ({ args; type' = _ } : append) =
      Sexp.List (Sexp.Atom "++" :: List.map args ~f:sexp_of_t)

    and sexp_of_zip ({ zipArg; nestCount; type' } : zip) =
      Sexp.List
        [ Sexp.Atom [%string "zip"]
        ; Sexp.List [ Sexp.Atom "nests"; Sexp.Atom (Int.to_string nestCount) ]
        ; sexp_of_t zipArg
        ; Type.sexp_of_t type'
        ]

    and sexp_of_unzip ({ unzipArg; type' = _ } : unzip) =
      Sexp.List [ Sexp.Atom [%string "unzip"]; sexp_of_t unzipArg ]

    and sexp_of_t = function
      | Box box -> sexp_of_box box
      | Literal lit -> sexp_of_literal lit
      | ScalarPrimitive scalarPrimitive -> sexp_of_scalarPrimitive scalarPrimitive
      | TupleDeref tupleDeref -> sexp_of_tupleDeref tupleDeref
      | Tuple tuple -> sexp_of_tuple tuple
      | Ref ref -> sexp_of_ref ref
      | Frame frame -> sexp_of_frame frame
      | BoxValue boxValue -> sexp_of_boxValue boxValue
      | IndexLet indexLet -> sexp_of_indexLet indexLet
      | Let let' -> sexp_of_let let'
      | ReifyIndex reifyIndex -> sexp_of_reifyIndex reifyIndex
      | ShapeProd shape ->
        Sexp.List [ Sexp.Atom "shape-prod"; [%sexp_of: Index.shape] shape ]
      | LoopBlock loopBlock -> sexp_of_loopBlock loopBlock
      | ContiguousSubArray contiguousSubArray ->
        sexp_of_contiguousSubArray contiguousSubArray
      | Append append -> sexp_of_append append
      | Zip zip -> sexp_of_zip zip
      | Unzip unzip -> sexp_of_unzip unzip
    ;;
  end

  include Sexp_of
end

type t = Expr.t

let sexp_of_t = Expr.sexp_of_t

module Substitute = struct
  module Index = Typed.Substitute.Index

  module Type = struct
    let rec subIndicesIntoArray indices Type.{ element; size } =
      let shape = Index.subIndicesIntoShape indices [ size ] in
      let rec makeArray shape =
        match shape with
        | [] -> element
        | size :: restShape -> Type.Array { element = makeArray restShape; size }
      in
      makeArray shape

    and subIndicesIntoType indices =
      let open Type in
      function
      | Sigma sigma -> Sigma (subIndicesIntoSigma indices sigma)
      | Literal (IntLiteral size) -> Literal (IntLiteral size)
      | Literal FloatLiteral -> Literal FloatLiteral
      | Literal CharacterLiteral -> Literal CharacterLiteral
      | Literal BooleanLiteral -> Literal BooleanLiteral
      | Literal StringLiteral -> Literal StringLiteral
      | Array array -> subIndicesIntoArray indices array
      | Tuple elements -> Tuple (List.map elements ~f:(subIndicesIntoType indices))

    and subIndicesIntoSigma indices Type.{ parameters; body } =
      Type.{ parameters; body = subIndicesIntoType indices body }
    ;;

    let rec subTypesIntoArray types Type.{ element; size } =
      Type.{ element = subTypesIntoType types element; size }

    and subTypesIntoType types =
      let open Type in
      function
      | Sigma sigma -> Sigma (subTypesIntoSigma types sigma)
      | Literal (IntLiteral size) -> Literal (IntLiteral size)
      | Literal FloatLiteral -> Literal FloatLiteral
      | Literal CharacterLiteral -> Literal CharacterLiteral
      | Literal BooleanLiteral -> Literal BooleanLiteral
      | Literal StringLiteral -> Literal StringLiteral
      | Array array -> Array (subTypesIntoArray types array)
      | Tuple elements -> Tuple (List.map elements ~f:(subTypesIntoType types))

    and subTypesIntoSigma types Type.{ parameters; body } =
      Type.{ parameters; body = subTypesIntoType types body }
    ;;
  end
end
