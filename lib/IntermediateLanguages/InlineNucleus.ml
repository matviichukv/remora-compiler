(* open! Base

(* The ExplicitNucleus language represents a Remora program where maps have been made explicit *)

type 't param = 't Nucleus.param [@@deriving sexp]

module Index = Nucleus.Index
module Type = Nucleus.Type

module Expr = struct
  type ref =
    { id : Identifier.t
    ; type' : Type.array [@sexp_drop_if fun _ -> true]
    }
  [@@deriving sexp]

  type functionRef =
    { id : Identifier.t
    ; type' : Type.func [@sexp_drop_if fun _ -> true]
    }
  [@@deriving sexp]

  type scalar =
    { element : atom
    ; type' : Type.arr [@sexp_drop_if fun _ -> true]
    }

  and frame =
    { dimensions : int list
    ; elements : array list
    ; type' : Type.arr [@sexp_drop_if fun _ -> true]
    }

  and termApplication =
    { func : array
    ; args : array list
    ; type' : Type.arr [@sexp_drop_if fun _ -> true]
    }

  and typeApplication =
    { tFunc : array
    ; args : Type.t list
    ; type' : Type.arr [@sexp_drop_if fun _ -> true]
    }

  and indexApplication =
    { iFunc : array
    ; args : Index.t list
    ; type' : Type.arr [@sexp_drop_if fun _ -> true]
    }

  and unbox =
    { indexBindings : Identifier.t list
    ; valueBinding : Identifier.t
    ; box : array
    ; body : array
    ; type' : Type.arr [@sexp_drop_if fun _ -> true]
    }

  and termLambda = { type' : Type.func [@sexp_drop_if fun _ -> true] }

  and typeLambda =
    { params : Kind.t param list
    ; body : array
    ; type' : Type.forall [@sexp_drop_if fun _ -> true]
    }

  and indexLambda =
    { params : Sort.t param list
    ; body : array
    ; type' : Type.pi [@sexp_drop_if fun _ -> true]
    }

  and box =
    { indices : Index.t list
    ; body : array
    ; bodyType : Type.array
    ; type' : Type.sigma [@sexp_drop_if fun _ -> true]
    }

  and tupleLet =
    { params : Type.atom param list
    ; value : array
    ; body : array
    ; type' : Type.array [@sexp_drop_if fun _ -> true]
    }

  and tuple =
    { elements : atom list
    ; type' : Type.tuple [@sexp_drop_if fun _ -> true]
    }

  and mapArg =
    { binding : Identifier.t
    ; value : array
    }

  and reduceArg =
    { firstBinding : Identifier.t
    ; firstValue : array
    ; secondBinding : Identifier.t
    ; secondValue : array
    }

  and builtInFunction = NolamNucleus.Expr.builtInFunction

  and binop =
    | Add
    | Sub
    | Mul
    | Div

  and builtInFunctionCall =
    | Length of
        { arg : array
        ; t : Type.atom
        ; d : Index.dimension
        ; cellShape : Index.shape
        ; type' : Type.array [@sexp_drop_if fun _ -> true]
        }
    | Reduce of
        { body : array
        ; args : reduceArg list
        ; t : Type.atom
        ; dSub1 : Index.dimension
        ; itemPad : Index.shape
        ; cellShape : Index.shape
        ; type' : Type.array [@sexp_drop_if fun _ -> true]
        }
    | Map of
        { body : array
        ; args : mapArg list
        ; frameShape : Index.shape
        ; type' : Type.array [@sexp_drop_if fun _ -> true]
        }
    | Binop of
        { op : binop
        ; arg1 : array
        ; arg2 : array
        ; type' : Type.array [@sexp_drop_if fun _ -> true]
        }

  and literal = Nucleus.Expr.literal

  and array =
    | Ref of ref
    | Scalar of scalar
    | Frame of frame
    | TypeApplication of typeApplication
    | IndexApplication of indexApplication
    | Unbox of unbox
    | TupleLet of tupleLet
    | BuiltInFunction of builtInFunction
    | BuiltInFunctionCall of builtInFunctionCall

  and atom =
    | TermLambda of termLambda
    | TypeLambda of typeLambda
    | IndexLambda of indexLambda
    | Box of box
    | Tuple of tuple
    | Literal of literal

  and t =
    | Array of array
    | Atom of atom
  [@@deriving sexp]

  let atomType : atom -> Type.atom = function
    | TermLambda termLambda -> Func termLambda.type'
    | TypeLambda typeLambda -> Forall typeLambda.type'
    | IndexLambda indexLambda -> Pi indexLambda.type'
    | Box box -> Sigma box.type'
    | Tuple tuple -> Tuple tuple.type'
    | Literal (IntLiteral _) -> Literal IntLiteral
    | Literal (CharacterLiteral _) -> Literal CharacterLiteral
  ;;

  let arrayType : array -> Type.array = function
    | Ref ref -> ref.type'
    | Scalar scalar -> Arr scalar.type'
    | Frame frame -> Arr frame.type'
    | TypeApplication typeApplication -> Arr typeApplication.type'
    | IndexApplication indexApplication -> Arr indexApplication.type'
    | Unbox unbox -> Arr unbox.type'
    | TupleLet tupleLet -> tupleLet.type'
    | BuiltInFunction builtIn -> builtIn.type'
    | BuiltInFunctionCall call ->
      (match call with
       | Length length -> length.type'
       | Reduce reduce -> reduce.type'
       | Map map -> map.type'
       | Binop binop -> binop.type')
  ;;

  let type' : t -> Type.t = function
    | Array array -> Array (arrayType array)
    | Atom atom -> Atom (atomType atom)
  ;;
end

type t = Expr.array [@@deriving sexp]

module ShowStage (SB : Source.BuilderT) = struct
  type state = CompilerState.state
  type error = (SB.source option, string) Source.annotate
  type input = t
  type output = string

  let name = "Print NolamNucleus"
  let run input = CompilerPipeline.S.return (Sexp.to_string_hum ([%sexp_of: t] input))
end *)
