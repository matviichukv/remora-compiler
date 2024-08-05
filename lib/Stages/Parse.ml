open! Base
open MResult

module type S = sig
  type source
  type error = string * source
  type 't result = ('t, error) MResult.t

  val parseString : string -> source Ast.t result
  val parseFile : string -> source Ast.t result

  val parseTypeBinding
    :  string
    -> (source, (source, (source, Kind.t) Source.annotate) Ast.param) Source.annotate
       result

  val parseIndexBinding
    :  string
    -> (source, (source, (source, Sort.t) Source.annotate) Ast.param) Source.annotate
       result

  val parseType : string -> source Ast.Type.t result
  val parseIndex : string -> source Ast.Index.t result
end

module Make (SB : Source.BuilderT) = struct
  type source = SB.source
  type error = string * SB.source
  type 't result = ('t, error) MResult.t

  module Lexer = EsexpLexer.Make (SB)
  module Parser = RemoraParser.Make (SB)

  let parseBufferF (lexbuf : Lexing.lexbuf) f =
    try MOk (f Lexer.read lexbuf) with
    | Lexer.SyntaxError (msg, source) -> MResult.err (msg, source)
    | Parser.Error ->
      let src = SB.make ~start:lexbuf.lex_curr_p ~finish:lexbuf.lex_curr_p in
      MResult.err ([%string "Syntax error when parsing at %{SB.show src}"], src)
  ;;

  let parseBuffer lexbuf =
    try MOk (Parser.prog Lexer.read lexbuf) with
    | Lexer.SyntaxError (msg, source) -> MResult.err (msg, source)
    | Parser.Error ->
      let src = SB.make ~start:lexbuf.lex_curr_p ~finish:lexbuf.lex_curr_p in
      MResult.err ([%string "Syntax error when parsing at %{SB.show src}"], src)
  ;;

  let parseString str =
    let lexbuf = Lexing.from_string ~with_positions:true str in
    parseBuffer lexbuf
  ;;

  let parseFile filename =
    let channel = In_channel.open_text filename in
    let lexbuf = Lexing.from_channel ~with_positions:true channel in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
    let result = parseBuffer lexbuf in
    In_channel.close channel;
    result
  ;;

  let parseTypeBinding str =
    let lexbuf = Lexing.from_string ~with_positions:true str in
    parseBufferF lexbuf Parser.type_binding
  ;;

  let parseIndexBinding str =
    let lexbuf = Lexing.from_string ~with_positions:true str in
    parseBufferF lexbuf Parser.index_binding
  ;;

  let parseType str =
    let lexbuf = Lexing.from_string ~with_positions:true str in
    parseBufferF lexbuf Parser.tpe
  ;;

  let parseIndex str =
    let lexbuf = Lexing.from_string ~with_positions:true str in
    parseBufferF lexbuf Parser.index
  ;;
end

module Default = Make (Source.Builder)

module Unit = Make (struct
    type source = unit

    let make ~start:_ ~finish:_ = ()
    let merge () () = ()
    let between () () = ()
    let show () = ""
  end)

module Stage (SB : Source.BuilderT) = struct
  module Parser = Make (SB)

  type state = CompilerState.state
  type input = string
  type output = SB.source Ast.t
  type error = (SB.source option, string) Source.annotate

  let name = "Parse"

  let run input =
    CompilerPipeline.S.returnF
      (match Parser.parseString input with
       | MOk _ as expr -> expr
       | Errors errs ->
         Errors
           (NeList.map errs ~f:(fun (elem, source) ->
              Source.{ elem; source = Some source })))
  ;;
end
