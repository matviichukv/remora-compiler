%parameter <SourceBuilder : Source.BuilderT>

%{
open! Base
open Ast

type source = Source.t
%}

(* Constants *)
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> CONSTANT_STRING // TODO: rename to SymbolLiteral or QuotedSymbol
%token TRUE
%token FALSE
(* Parens *)
%token LEFT_PAREN
%token RIGHT_PAREN
%token LEFT_SQUARE
%token RIGHT_SQUARE
%token LEFT_CURLY
%token RIGHT_CURLY
(* Misc chars *)
%token BAR
%token COLON
(* Keywords *)
%token DEFINE
%token ARRAY
%token FRAME
%token LET
%token REIFY_SHAPE
%token REIFY_DIMENSION
%token RESHAPE
%token LIFT
%token BOX
%token BOXES
%token UNBOX
%token VALUES
%token <int> TUPLE_DEREF
%token T_APP
%token I_APP
%token LAMBDA
%token T_LAMBDA
%token I_LAMBDA
%token TYPE_ARR
%token TYPE_FORALL
%token TYPE_PI
%token TYPE_SIGMA
%token TYPE_VALUES
%token RIGHT_ARROW
%token PLUS
%token APPEND
%token SHAPE
(* Variables *)
%token <string> SYMBOL
(* the rest *)
%token EOF
%start <SourceBuilder.source Ast.t> progIntro

(* Type decls for non terminals *)
%type <(source, source Ast.t) Source.annotate> expr

%%
progIntro:
  | p = prog { p }

prog:
  | defns = list(define); e = expr; EOF
    {
      List.fold_right defns ~init:e ~f:(fun { elem = (binding, bound, value); source = sourceLet }
                                            acc ->
        let param = Source.{ elem = { binding; bound }
                           ; source = SourceBuilder.merge binding.source bound.source }
        in
        Source.{ elem = Expr.Let { param; value; body = acc }
               ; source = SourceBuilder.merge sourceLet acc.source })
    }

expr:
  | constant = const { constant }
  | var = sym { var }
  | LEFT_PAREN; REIFY_SHAPE; shape = index; RIGHT_PAREN
    { Source.{ elem = Expr.ReifyShape shape
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; REIFY_DIMENSION; shape = index; RIGHT_PAREN
    { Source.{ elem = Expr.ReifyDimension shape
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; LET; LEFT_SQUARE; binding = binding; bound = option(type_ann);
                                   value = expr; RIGHT_SQUARE;
                     body = nonempty_list(expr); RIGHT_PAREN
    { let param = Source.{ elem = { binding; bound }
                         ; source = SourceBuilder.make ~start:$startpos(binding) ~finish:$endpos(binding) } in
      Source.{ elem = Expr.Let { param; value; body } } }
  (* Figure out what we are doing here *)
  (* | LEFT_PAREN; (ARRAY | FRAME); LEFT_SQUARE; dimensions = list(const_dim); RIGHT_SQUARE; *)
  (*                      elements = list(); RIGHT_PAREN { ??? } *)
  | LEFT_SQUARE; hd_expr = expr; tl_expr = list(expr); RIGHT_SQUARE
    { let source = SourceBuilder.make ~start:$startpos ~finish:$endpos in
      let all : _ NeList.t = hd_expr :: tl_expr in
      Source.{ elem = Expr.Frame { dimensions = { elem = [ { elem = { elem = NeList.length all; source }
                                                           ; source }]
                                                ; source}
                                 ; elements = hd_expr :: tl_expr }; source } }
  | LEFT_PAREN; LIFT; LEFT_SQUARE; indexBinding = index_binding; indexValue = expr; RIGHT_SQUARE;
                      body = body_expr; RIGHT_PAREN
    { let { binding = indexBinding; bound = sort } = indexBinding.elem in
      Source.{ elem = Expr.Lift { indexBinding; indexValue; sort; body  }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  /* | LEFT_PAREN; BOX; ; RIGHT_PAREN { ??? } */
  /* | LEFT_PAREN; BOXES; ...; RIGHT_PAREN { ??? } */
  /* | LEFT_PAREN; UNBOX; ...; RIGHT_PAREN { ??? } */
  | LEFT_PAREN; VALUES; elements = list(expr); RIGHT_PAREN
    { let elements = Source.{ elem = elements
                            ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos }
      in
      Source.{ elem = Expr.TupleExpr elements
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; position = TUPLE_DEREF; tuple = expr; RIGHT_PAREN
    { Source.{ elem = Expr.TupleDeref { tuple; position }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | e = expr; LEFT_CURLY; typeArgs = list(tpe); RIGHT_CURLY;
              LEFT_CURLY; indexArgs = list(index); RIGHT_CURLY;
    {
      let annIndexArgs = Source.{ elem = indexArgs
                                ; source = SourceBuilder.make ~start:$startpos(indexArgs) ~finish:$endpos(indexArgs) } in
      let annTypeArgs = Source.{ elem = typeArgs
                               ; source = SourceBuilder.make ~start:$startpos(typeArgs) ~finish:$endpos(typeArgs) } in
      let e = match indexArgs with
              | [] -> e
              | _  -> Source.{ elem = Expr.IndexApplication { iFunc = e; args = annIndexArgs } }
      in
      match typeArgs with
        | [] -> e
        | _  -> Source.{ elem = Expr.TypeApplication { tFunc = e; args = annTypeArgs } }
    }
  | LEFT_PAREN; func = expr; args = list(expr); RIGHT_PAREN
  | LEFT_PAREN; func = keyword_as_ref; args = list(expr); RIGHT_PAREN
    {
      let args = Source.{ elem = args
                        ; source = SourceBuilder.make ~start:$startpos(args) ~finish:$endpos(args) } in
      Source.{ elem = Expr.TermApplication { func; args }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos }
    }
  | LEFT_PAREN; T_APP; tFunc = expr; args = list(tpe); RIGHT_PAREN
    { let args = Source.{ elem = args
                        ; source = SourceBuilder.make ~start:$startpos(args) ~finish:$endpos(args) }
      in
      Source.{ elem = Expr.TypeApplication { tFunc; args } } }
  | LEFT_PAREN; I_APP; iFunc = expr; args = list(index); RIGHT_PAREN
    { let args = Source.{ elem = args
                        ; source = SourceBuilder.make ~start:$startpos(args) ~finish:$endpos(args) }
      in
      Source.{ elem = Expr.IndexApplication { iFunc; args } } }
  | LEFT_PAREN; LAMBDA; LEFT_PAREN; params = list(param_binding); RIGHT_PAREN;
                        retType = option(type_ann);
                        body = body_expr; RIGHT_PAREN
    { let params = Source.{ elem = params
                          ; source = SourceBuilder.make ~start:$startpos(params) ~finish:$endpos(params) } in
      Source.{ elem = Expr.TermLambda { params; body; returnTypeOpt = retType }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; T_LAMBDA; LEFT_PAREN; params = list(type_binding); RIGHT_PAREN;
                          body = body_expr; RIGHT_PAREN
    { let params = Source.{ elem = params
                          ; source = SourceBuilder.make ~start:$startpos(params) ~finish:$endpos(params) } in
      Source.{ elem = Expr.TypeLambda { params; body }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; I_LAMBDA; LEFT_PAREN; params = list(index_binding); RIGHT_PAREN;
                          body = body_expr; RIGHT_PAREN
    { let params = Source.{ elem = params
                          ; source = SourceBuilder.make ~start:$startpos(params) ~finish:$endpos(params) } in
      Source.{ elem = Expr.IndexLambda { params; body }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }

const:
  | i = INT    { Source.{ elem = IntLiteral i; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | f = FLOAT  { Source.{ elem = FloatLiteral f; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | TRUE   { Source.{ elem = BooleanLiteral true; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | FALSE  { Source.{ elem = BooleanLiteral false; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | cs = CONSTANT_STRING { Source.{ elem = StringLiteral cs
                                  ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | s = STRING
    { let source = SourceBuilder.make ~start:$startpos ~finish:$endpos in
      match String.to_list s with
        | [] -> { elem = Expr.EmptyArr { dimensions = { elem = [ { elem = 0; source } ]; source }
                                       ; elementType = { elem = Type.Ref "char"; source } }
                ; source }
        | hd :: tl ->
           Source.{ elem = Expr.Arr { elements = { elem = NeList.map (hd :: tl) ~f:(fun c -> Source.{ elem = Expr.CharacterLiteral c; source }) }
                                    ; dimensions = { elem = [ { elem = List.length (hd :: tl); source } ]; source } }
                  ; source } }

const_dim:
  | dim = INT { Source.{ elem = dim
                       ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }

binding:
  | id = SYMBOL
    { if String.is_prefix id ~prefix:"@"
      then error
      else Source.{ elem = id
                  ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }

index:
  | i = INT     { Source.{ elem = Index.Dimension i
                         ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | id = SYMBOL { Source.{ elem = Index.Ref id
                         ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; PLUS; indices = list(index); RIGHT_PAREN
    { Source.{ elem = Index.Add indices
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; APPEND; indices = list(index); RIGHT_PAREN
    { Source.{ elem = Index.Append indices
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; SHAPE; indices = list(index); RIGHT_PAREN
    { Source.{ elem = Index.Shape indices
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_SQUARE; indices = list(index); RIGHT_SQUARE
    { Source.{ elem = Index.Slice indices;
               source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }

tpe:
  | id = SYMBOL { Source.{ elem = Type.Ref id
                         ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; TYPE_ARR; elementType = tpe; shape = index; RIGHT_PAREN
    { Source.{ elem = Type.Arr { element = elementType; shape }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; RIGHT_ARROW; LEFT_PAREN; parameters = list(tpe); RIGHT_PAREN;
                             return = tpe; RIGHT_PAREN
    { Source.{ elem = Type.Func { parameters; return }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; TYPE_FORALL; LEFT_PAREN; parameters = list(type_binding); RIGHT_PAREN;
                                         body = tpe; RIGHT_PAREN
    { Source.{ elem = Type.Forall ( Type.{ parameters; body } )
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; TYPE_PI; LEFT_PAREN; paramenters = list(index_binding); RIGHT_PAREN;
                                     body = tpe; RIGHT_PAREN
    { Source.{ elem = Type.Pi ( Type.{ parameters; body } )
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; TYPE_SIGMA; LEFT_PAREN; paramenters = list(index_binding); RIGHT_PAREN;
                                        body = tpe; RIGHT_PAREN
    { Source.{ elem = Type.Sigma ( Type.{ parameters; body } )
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_PAREN; TYPE_VALUES; tuple = list(tpe); RIGHT_PAREN
    { Source.{ elem = Type.Tuple tuple
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | LEFT_SQUARE; elementType = tpe; shapeElements = list(index); RIGHT_SQUARE
    { Source.{ elem = Type.Arr { element = elementType
                               ; shape = Index.Slice shapeElements }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }

param_binding:
  | LEFT_PAREN; binding = binding; bound = tpe; RIGHT_PAREN
    { Source.{ elem = { binding; bound }
             ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }

type_binding:
  | binding = sym
    {
      let source = SourceBuilder.make ~start:$startpos ~finish:$endpos in
      let bound = if String.is_prefix id ~prefix:"@" then Kind.Array else Kind.Atom in
      let bound = Source.{ elem = bound; source } in
      Source.{ elem = { binding; bound }; source }
    }

index_binding:
  | binding = sym
    {
      let source = SourceBuilder.make ~start:$startpos ~finish:$endpos in
      let bound = if String.is_prefix id ~prefix:"@" then Sort.Shape else Sort.Dim in
      let bound = Source.{ elem = bound; source } in
      Source.{ elem = { binding; bound }; source }
    }

define:
  | LEFT_PAREN; DEFINE; binding = sym;
                        bound = option(type_ann);
                        value = expr; RIGHT_PAREN
    { binding, bound, value }
  | LEFT_PAREN; DEFINE; LEFT_PAREN; func_name = sym;
                                    iAndTParams = option(fn_t_and_i_decl);
                                    params = list(fn_decl_binding)
                                    RIGHT_PAREN;
                        returnTypeOpt = option(type_ann);
                        body = body_expr; RIGHT_PAREN
    {
      let source = SourceBuilder.make ~start:$startpos ~finish:$endpos in
      let body = Source.{ elem = Expr.TermLambda { params; body; returnTypeOpt }
                        ; source }
      in
      match iAndTParams with
        | None -> func_name, None, body
        | Some iAndTParams ->
          let iParams, tParams = iAndTParams in
          let body = match tParams with
            | [] -> body
            | _  -> Source.{ elem = Expr.TypeLambda { params = tParams; body }
                           ; source }
          in
          let body = match iParams with
            | [] -> body
            | _  -> Source.{ elem = Expr.IndexLambda { params = iParams; body }
                           ; source }
          in
          (func_name, None, body)
    }

fn_t_and_i_decl:
  | LEFT_CURLY; tParams = list(type_binding); RIGHT_CURLY;
    LEFT_CURLY; iParams = list(index_binding); RIGHT_CURLY
    {
      (Source.{ elem = tParams
             ; source = SourceBuilder.make ~start:$startpos(tParams) ~finish:$endpos(tParams) },
      Source.{ elem = iParams
             ; source = SourceBuilder.make ~start:$startpos(iParams) ~finish:$endpos(iParams) })
    }

fn_decl_binding:
  | LEFT_SQUARE; variable = sym; tpe = tpe; RIGHT_SQUARE
    { variable, tpe }

keyword_as_ref:
  | PLUS { Source.{ elem = Expr.Ref "+"
                  ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | APPEND { Source.{ elem = Expr.Ref "++"
                    ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | TYPE_PI { Source.{ elem = Expr.Ref "Pi"
                     ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | TYPE_SIGMA { Source.{ elem = Expr.Ref "Sigma"
                        ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | TYPE_ARR { Source.{ elem = Expr.Ref "Arr"
                      ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | TYPE_FORALL { Source.{ elem = Expr.Ref "Forall"
                         ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | TYPE_VALUES { Source.{ elem = Expr.Ref "Values"
                         ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }
  | SHAPE { Source.{ elem = Expr.Ref "shape"
                   ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }

sym:
  | id = SYMBOL { Source.{ elem = id
                         ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }

type_ann:
  | COLON; tpe = tpe
           { Source.{ elem = tpe
                    ; source = SourceBuilder.make ~start:$startpos ~finish:$endpos } }

body_expr:
  | hd = expr; tl = list(expr)
    { let body : _ NeList.t = hd :: tl in
      Source.{ elem = body
             ; source = SourceBuilder.make ~start:$startpos(hd) ~finish:$endpos(tl) } }
