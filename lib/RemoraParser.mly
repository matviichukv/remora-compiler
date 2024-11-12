%parameter <SourceBuilder : Source.BuilderT>

%{
module Remora = struct end
(* open! Base *)
open Ast

let makeSource (start, finish) = SourceBuilder.make ~start ~finish
let makeAnn elem loc = Source.{ elem; source = makeSource loc }
let makeAnnSource elem source = Source.{ elem; source }

%}

(* Constants *)
%token <int> INT
%token ZERO
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
%token LET_STAR
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
%start <SourceBuilder.source Ast.t> prog
(* These are not actual start tokens, they are here to parse base env stuff *)
%start <(SourceBuilder.source, (SourceBuilder.source, (_, Kind.t) Source.annotate) Ast.param) Source.annotate> type_binding
%start <(SourceBuilder.source, (SourceBuilder.source, (_, Sort.t) Source.annotate) Ast.param) Source.annotate> index_binding
%start <SourceBuilder.source Ast.Type.t> tpe
%start <SourceBuilder.source Ast.Index.t> index

%%
prog:
  | p = body_expr; EOF { p }

body_expr:
  | define = define; body = body_expr
    { let Source.{ elem = (binding, bound, value); source = sourceDefine } = define in
      let param = makeAnn { binding; bound } $loc(define) in
      makeAnnSource (Expr.Let { param; value; body })
                    (SourceBuilder.merge sourceDefine body.source) }
   | e = expr { e }

expr:
  | constant = const { constant }
  | s = sym { Source.{ elem = Expr.Ref s.elem; source = s.source } }
  | k = keyword_as_ref { k }
  | LEFT_PAREN; REIFY_SHAPE; shape = index; RIGHT_PAREN
    { makeAnn (Expr.ReifyShape shape) $loc }
  | LEFT_PAREN; REIFY_DIMENSION; shape = index; RIGHT_PAREN
    { makeAnn (Expr.ReifyDimension shape) $loc }
  | LEFT_PAREN; RESHAPE; newShape = index; value = expr; RIGHT_PAREN
    { makeAnn (Expr.Reshape { newShape; value }) $loc }
  | LEFT_PAREN; LET_STAR; LEFT_PAREN; bindings = list(let_binding); RIGHT_PAREN;
                          body = body_expr; RIGHT_PAREN
    { Base.List.fold_right bindings ~init:body
                           ~f:(fun (param, value) acc ->
                                makeAnnSource (Expr.Let {param; value; body = acc})
                                              (SourceBuilder.merge param.source acc.source)) }
  | LEFT_PAREN; LET; let_binding = let_binding;
                     body = body_expr; RIGHT_PAREN
    { let (param, value) = let_binding in
      makeAnn (Expr.Let { param; value; body }) $loc }
  (* Empty array/frame *)
  | LEFT_PAREN; ARRAY; dimensions = dimensions_of_empty; elementType = tpe; RIGHT_PAREN
    { makeAnn (Expr.EmptyArr { elementType; dimensions }) $loc }
  | LEFT_PAREN; FRAME; dimensions = dimensions_of_empty; elementType = tpe; RIGHT_PAREN
    { makeAnn (Expr.EmptyArr { elementType; dimensions }) $loc }
  (* Non empty array/frame *)
  | LEFT_PAREN; ARRAY; dimensions = dimensions; elements = ann_ne_list(expr); RIGHT_PAREN
    { makeAnn ( Expr.Arr { dimensions; elements }) $loc }
  | LEFT_PAREN; FRAME; dimensions = dimensions; elements = ann_ne_list(expr); RIGHT_PAREN
    { makeAnn ( Expr.Frame { dimensions; elements }) $loc }
  | LEFT_SQUARE; hd_expr = expr; tl_expr = list(expr); RIGHT_SQUARE
    { let elements : _ NeList.t = hd_expr :: tl_expr in
      makeAnn (Expr.Frame { dimensions = makeAnn [ makeAnn (NeList.length elements) $loc ] $loc
                          ; elements = makeAnn elements $loc })
              $loc }
  | LEFT_PAREN; LIFT; LEFT_SQUARE; indexBinding = index_binding; indexValue = expr; RIGHT_SQUARE;
                      body = body_expr; RIGHT_PAREN
    { let Source.{ elem = { binding; bound }; source = _ } = indexBinding in
      makeAnn (Expr.Lift { indexBinding = binding; indexValue; sort = bound; body }) $loc }
  | LEFT_PAREN; BOX; LEFT_PAREN; args = list(index_param_binding); RIGHT_PAREN;
                     elementType = tpe; body = body_expr; RIGHT_PAREN
    { let params, indices = Base.List.unzip args in
      let params = makeAnn params $loc in
      let indices = makeAnn indices $loc in
      makeAnn (Expr.Boxes { params
                          ; elementType
                          ; dimensions = makeAnn [] $loc
                          ; elements = makeAnn [makeAnn Expr.{indices; body} $loc] $loc })
              $loc
     }
  | LEFT_PAREN; BOXES; LEFT_PAREN; params = ann_list(index_binding); RIGHT_PAREN;
                       elementType = tpe;
                       dimensions = dimensions;
                       elements = ann_list(boxes_element);
                       RIGHT_PAREN
    { makeAnn (Expr.Boxes { params; elementType; dimensions; elements }) $loc }
  | LEFT_PAREN; UNBOX; box = expr;
                       LEFT_PAREN; valueBinding = binding;
                                   indexBindings = list(index_binding);
                       RIGHT_PAREN
                       body = body_expr;
    RIGHT_PAREN
    (* TODO: i don't think this has to be option since in original parser is was always Some *)
    { let indexBindings =
        Base.List.map indexBindings
                      ~f:(fun Source.{ elem = { binding; bound }; source } ->
                            Source.{ elem = Expr.{ binding; bound = Some bound }; source } ) in
      let indexBindings = makeAnn indexBindings $loc(indexBindings) in
      makeAnn (Expr.Unbox { valueBinding; indexBindings; box; body }) $loc
    }
  | LEFT_PAREN; VALUES; elements = ann_list(expr); RIGHT_PAREN
    { makeAnn (Expr.ValuesExpr elements) $loc }
  | LEFT_PAREN; position = TUPLE_DEREF; e = expr; RIGHT_PAREN
    { makeAnn (Expr.ValuesDeref { expr = e; position }) $loc }
  | e = expr; LEFT_CURLY; typeArgs = list(tpe); RIGHT_CURLY;
              LEFT_CURLY; indexArgs = list(index); RIGHT_CURLY
  | e = expr; LEFT_CURLY; typeArgs = list(tpe); BAR
                        ; indexArgs = list(index); RIGHT_CURLY
    { let annIndexArgs = makeAnn indexArgs $loc(indexArgs) in
      let annTypeArgs = makeAnn typeArgs $loc(typeArgs) in
      let e = match indexArgs with
              | [] -> e
              | _  -> makeAnn (Expr.IndexApplication { iFunc = e; args = annIndexArgs } )
                              $loc(indexArgs)
      in
      match typeArgs with
      | [] -> e
      | _  -> makeAnn (Expr.TypeApplication { tFunc = e; args = annTypeArgs })
                      $loc(typeArgs) }
  | LEFT_PAREN; func = expr; args = ann_list(expr); RIGHT_PAREN
  /* | LEFT_PAREN; func = keyword_as_ref; args = ann_list(expr); RIGHT_PAREN */
    { makeAnn (Expr.TermApplication { func; args }) $loc }
  | LEFT_PAREN; T_APP; tFunc = expr; args = ann_list(tpe); RIGHT_PAREN
    { makeAnn (Expr.TypeApplication { tFunc; args }) $loc }
  | LEFT_PAREN; I_APP; iFunc = expr; args = ann_list(index); RIGHT_PAREN
    { makeAnn (Expr.IndexApplication { iFunc; args }) $loc }
  | LEFT_PAREN; LAMBDA; LEFT_PAREN; params = ann_list(param_binding); RIGHT_PAREN;
                        returnTypeOpt = option(type_ann);
                        body = body_expr; RIGHT_PAREN
    { makeAnn (Expr.TermLambda { params; body; returnTypeOpt }) $loc }
  | LEFT_PAREN; T_LAMBDA; LEFT_PAREN; params = ann_list(type_binding); RIGHT_PAREN;
                          body = body_expr; RIGHT_PAREN
    { makeAnn (Expr.TypeLambda { params; body }) $loc }
  | LEFT_PAREN; I_LAMBDA; LEFT_PAREN; params = ann_list(index_binding); RIGHT_PAREN;
                          body = body_expr; RIGHT_PAREN
    { makeAnn (Expr.IndexLambda { params; body }) $loc }

let_binding:
  | LEFT_SQUARE; binding = binding; bound = option(type_ann); value = expr; RIGHT_SQUARE
    { let param = makeAnn { binding; bound } $loc in
      param, value }

boxes_element:
  | LEFT_PAREN; LEFT_PAREN; indices = ann_list(index); RIGHT_PAREN; body = body_expr; RIGHT_PAREN
    { makeAnn Expr.{indices; body} $loc }

dimensions_of_empty:
  | LEFT_SQUARE; left = list(const_dim); z = ZERO; right = list(const_dim); RIGHT_SQUARE
    { let _ = z in makeAnn (Base.List.append left ((makeAnn 0 $loc(z)) :: right)) $loc }

dimensions:
  | LEFT_SQUARE; dims = ann_list(const_dim); RIGHT_SQUARE { dims }

const:
  | ZERO      { makeAnn (Expr.IntLiteral 0) $loc }
  | i = INT   { makeAnn (Expr.IntLiteral i) $loc }
  | f = FLOAT { makeAnn (Expr.FloatLiteral f) $loc }
  | TRUE      { makeAnn (Expr.BooleanLiteral true) $loc }
  | FALSE     { makeAnn (Expr.BooleanLiteral false) $loc }
  | cs = CONSTANT_STRING { makeAnn (Expr.StringLiteral cs) $loc }
  | s = STRING
    { let open! Base in
      match String.to_list s with
      | [] -> makeAnn (Expr.EmptyArr { dimensions = makeAnn [ makeAnn 0 $loc ] $loc
                                     ; elementType = makeAnn (Ast.Type.Ref "char") $loc } )
                      $loc
      | hd :: tl ->
         let elements = NeList.map (hd :: tl) ~f:(fun c -> makeAnn (Expr.CharacterLiteral c) $loc) in
         makeAnn (Expr.Arr { elements = makeAnn elements $loc
                           ; dimensions = makeAnn [makeAnn (NeList.length elements) $loc] $loc })
                 $loc }

const_dim:
  | dim = INT { makeAnn dim $loc }

index:
  | ZERO        { makeAnn (Index.Dimension 0) $loc }
  | i = INT     { makeAnn (Index.Dimension i) $loc }
  | id = SYMBOL { makeAnn (Index.Ref id) $loc }
  | LEFT_PAREN; PLUS; indices = list(index); RIGHT_PAREN
    { makeAnn (Index.Add indices) $loc }
  | LEFT_PAREN; APPEND; indices = list(index); RIGHT_PAREN
    { makeAnn (Index.Append indices) $loc }
  | LEFT_PAREN; SHAPE; indices = list(index); RIGHT_PAREN
    { makeAnn (Index.Shape indices) $loc }
  | LEFT_SQUARE; indices = list(index); RIGHT_SQUARE
    { makeAnn (Index.Slice indices) $loc }

tpe:
  | id = SYMBOL { makeAnn (Type.Ref id) $loc }
  | LEFT_PAREN; TYPE_ARR; element = tpe; shape = index; RIGHT_PAREN
    { makeAnn (Type.Arr { element; shape }) $loc }
  | LEFT_PAREN; RIGHT_ARROW; LEFT_PAREN; parameters = ann_list(tpe); RIGHT_PAREN;
                             return = tpe; RIGHT_PAREN
    { makeAnn (Type.Func { parameters; return }) $loc }
  | LEFT_PAREN; TYPE_FORALL; LEFT_PAREN; parameters = ann_list(type_binding); RIGHT_PAREN;
                                         body = tpe; RIGHT_PAREN
    { makeAnn (Type.Forall ( Type.{ parameters; body } )) $loc }
  | LEFT_PAREN; TYPE_PI; LEFT_PAREN; parameters = ann_list(index_binding); RIGHT_PAREN;
                                     body = tpe; RIGHT_PAREN
    { makeAnn (Type.Pi ( Type.{ parameters; body } )) $loc }
  | LEFT_PAREN; TYPE_SIGMA; LEFT_PAREN; parameters = ann_list(index_binding); RIGHT_PAREN;
                                        body = tpe; RIGHT_PAREN
    { makeAnn (Type.Sigma (Type.{ parameters; body })) $loc }
  | LEFT_PAREN; TYPE_VALUES; tuple = ann_list(tpe); RIGHT_PAREN
    { makeAnn (Type.Tuple tuple) $loc }
  | LEFT_SQUARE; element = tpe; shapeElements = list(index); RIGHT_SQUARE
    { let shape = makeAnn (Index.Slice shapeElements) $loc(shapeElements) in
      makeAnn (Type.Arr { element; shape }) $loc }

param_binding:
  | LEFT_SQUARE; binding = binding; bound = tpe; RIGHT_SQUARE
    { makeAnn { binding; bound } $loc }

index_param_binding:
  | LEFT_PAREN; binding = index_binding; index = index; RIGHT_PAREN
    { binding, index }

binding:
  | id = SYMBOL
    { if Base.String.is_prefix id ~prefix:"@"
      then raise (Unreachable.Error "Variable binding should not start with @")
      else makeAnn id $loc }

type_binding:
  | id = SYMBOL
    { let binding = makeAnn id $loc in
      let bound = if Base.String.is_prefix id ~prefix:"@"
                  then Kind.Array
                  else Kind.Atom in
      let bound = makeAnn bound $loc in
      makeAnn { binding; bound } $loc }

index_binding:
  | id = SYMBOL
    { let binding = makeAnn id $loc in
      let bound = if Base.String.is_prefix id ~prefix:"@"
                  then Sort.Shape
                  else Sort.Dim in
      let bound = makeAnn bound $loc in
      makeAnn { binding; bound } $loc }

define:
  | LEFT_PAREN; DEFINE; binding = sym;
                        bound = option(type_ann);
                        value = expr; RIGHT_PAREN
    { makeAnn (binding, bound, value) $loc }
  | LEFT_PAREN; DEFINE; LEFT_PAREN; func_name = sym;
                                    params = ann_list(fn_decl_binding)
                                    RIGHT_PAREN;
                        returnTypeOpt = option(type_ann);
                        body = body_expr; RIGHT_PAREN
    { let body = makeAnn (Expr.TermLambda { params; body; returnTypeOpt }) $loc in
      makeAnn (func_name, None, body) $loc }
  | LEFT_PAREN; DEFINE; LEFT_PAREN; func_name = sym;
                                    tParams = fn_t_decl;
                                    iParams = fn_i_decl;
                                    params = ann_list(fn_decl_binding)
                                    RIGHT_PAREN;
                        returnTypeOpt = option(type_ann);
                        body = body_expr; RIGHT_PAREN
    { let body = makeAnn (Expr.TermLambda { params; body; returnTypeOpt }) $loc in
      let body = match tParams with
        | Source.{ elem = []; source = _ } -> body
        | _ -> makeAnn (Expr.TypeLambda { params = tParams; body }) $loc
      in
      let body = match iParams with
        | Source.{ elem = []; source = _ } -> body
        | _ -> makeAnn (Expr.IndexLambda { params = iParams; body }) $loc
      in
      makeAnn (func_name, None, body) $loc }
  | LEFT_PAREN; DEFINE; LEFT_PAREN; func_name = sym;
                                    LEFT_CURLY;
                                    tParams = ann_list(type_binding);
                                    BAR;
                                    iParams = ann_list(index_binding);
                                    RIGHT_CURLY;
                                    params = ann_list(fn_decl_binding)
                                    RIGHT_PAREN;
                        returnTypeOpt = option(type_ann);
                        body = body_expr; RIGHT_PAREN
    { let body = makeAnn (Expr.TermLambda { params; body; returnTypeOpt }) $loc in
      let body = match tParams with
        | Source.{ elem = []; source = _ } -> body
        | _ -> makeAnn (Expr.TypeLambda { params = tParams; body }) $loc
      in
      let body = match iParams with
        | Source.{ elem = []; source = _ } -> body
        | _ -> makeAnn (Expr.IndexLambda { params = iParams; body }) $loc
      in
      makeAnn (func_name, None, body) $loc }

fn_t_decl:
  | LEFT_CURLY; tParams = ann_list(type_binding); RIGHT_CURLY { tParams }

fn_i_decl:
  | LEFT_CURLY; iParams = ann_list(index_binding); RIGHT_CURLY { iParams }

fn_decl_binding:
  | LEFT_SQUARE; binding = sym; bound = tpe; RIGHT_SQUARE
    { makeAnn { binding; bound } $loc }

keyword_as_ref:
  | PLUS        { makeAnn (Expr.Ref "+") $loc }
  | APPEND      { makeAnn (Expr.Ref "++") $loc }
  | TYPE_PI     { makeAnn (Expr.Ref "Pi") $loc }
  | TYPE_SIGMA  { makeAnn (Expr.Ref "Sigma") $loc }
  | TYPE_ARR    { makeAnn (Expr.Ref "Arr") $loc }
  | TYPE_FORALL { makeAnn (Expr.Ref "Forall") $loc }
  | TYPE_VALUES { makeAnn (Expr.Ref "Values") $loc }
  | SHAPE       { makeAnn (Expr.Ref "shape") $loc }

sym:
  | id = SYMBOL { makeAnn id $loc }

type_ann:
  | COLON; tpe = tpe { tpe }

%inline ann_ne_list(X):
  | xs = nonempty_list(X)
    { makeAnn (Base.Option.value_exn (NeList.of_list xs)) $loc(xs) }

%inline ann_list(X):
  | xs = list(X) { makeAnn xs $loc(xs) }
