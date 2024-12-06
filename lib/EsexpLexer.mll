{
module Make (SourceBuilder : Source.BuilderT) = struct
  open Lexing
  module P = RemoraParser.Make(SourceBuilder)

  exception SyntaxError of string * SourceBuilder.source
}

let int = '-'? ['0'-'9']+
let posint = ['0'-'9']+
let floatLead = '-'? ['0'-'9'] ['0'-'9']* '.' ['0'-'9']*
let floatTrail = '-'? ['0'-'9']* '.' ['0'-'9'] ['0'-'9']*

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let unreservedchar = [^'(' ')' '[' ']' '{' '}' '"' ',' '\'' '`' ';' '|' '\\' ' ' '\t' '\r' '\n' '@']
let symbol = (unreservedchar | '@') unreservedchar*
let true = "#t" | "#true"
let false = "#f" | "#false"

rule read =
  parse
  | white    { read lexbuf }
  | newline  { new_line lexbuf; read lexbuf }
  (* Constants *)
  | int      { P.INT (int_of_string (Lexing.lexeme lexbuf)) }
  | (floatLead | floatTrail)    { P.FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
  | '\'' '|' { read_constant_string (Buffer.create 17) lexbuf }
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | true     { TRUE }
  | false    { FALSE }
  (* All the parens *)
  | '('      { LEFT_PAREN }
  | ')'      { RIGHT_PAREN }
  | '['      { LEFT_SQUARE }
  | ']'      { RIGHT_SQUARE }
  | '{'      { LEFT_CURLY }
  | '}'      { RIGHT_CURLY }
  (* Other misc stuff *)
  | '|'      { BAR }
  | ':'      { COLON }
  (* Comments *)
  | ';'      { read_single_line_comment lexbuf }
  | '#' '|'  { read_multi_line_comment lexbuf }
  (* Keywords and some other syntactic things *)
  | "define" { DEFINE }
  | "array"  { ARRAY }
  | "frame"  { FRAME }
  | "let"    { LET }
  | "let*"   { LET_STAR }
  | "reify-shape" { REIFY_SHAPE }
  | "reify-dimension" { REIFY_DIMENSION }
  | "reshape" { RESHAPE }
  | "lift"   { LIFT }
  | "box"    { BOX }
  | "boxes"  { BOXES }
  | "unbox"  { UNBOX }
  | "tuple"  { TUPLE }
  | '#' (posint as idx) { P.TUPLE_DEREF (int_of_string idx) }
  | "t-app"  { T_APP }
  | "i-app"  { I_APP }
  | "fn"     { LAMBDA }
  | "t-fn"   { T_LAMBDA }
  | "i-fn"   { I_LAMBDA }
  | "Arr"    { TYPE_ARR }
  | "Forall" { TYPE_FORALL }
  | "Pi"     { TYPE_PI }
  | "Sigma"  { TYPE_SIGMA }
  | "Tuple"  { TYPE_TUPLE }
  | "->"     { RIGHT_ARROW }
  | "+"      { PLUS }
  | "++"     { APPEND }
  | "shape"  { SHAPE }
  (* only symbols left are variables *)
  | symbol   { SYMBOL (Lexing.lexeme lexbuf) }
  | _        { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf, SourceBuilder.make ~start:(Lexing.lexeme_start_p lexbuf) ~finish:(Lexing.lexeme_end_p lexbuf))) }
  | eof      { EOF }

and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf, SourceBuilder.make ~start:(Lexing.lexeme_start_p lexbuf) ~finish:(Lexing.lexeme_end_p lexbuf))) }
  | eof { raise (SyntaxError ("String is not terminated", SourceBuilder.make ~start:(Lexing.lexeme_start_p lexbuf) ~finish:(Lexing.lexeme_end_p lexbuf))) }

and read_constant_string buf =
  parse
  | '|' { CONSTANT_STRING (Buffer.contents buf) }
  | '\\' '|'  { Buffer.add_char buf '|'; read_constant_string buf lexbuf }
  | '\\' '/'  { Buffer.add_char buf '/'; read_constant_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_constant_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_constant_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_constant_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_constant_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_constant_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_constant_string buf lexbuf }
  | [^ '|' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_constant_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal symbol character: " ^ Lexing.lexeme lexbuf, SourceBuilder.make ~start:(Lexing.lexeme_start_p lexbuf) ~finish:(Lexing.lexeme_end_p lexbuf))) }
  | eof { raise (SyntaxError ("Symbol is not terminated", SourceBuilder.make ~start:(Lexing.lexeme_start_p lexbuf) ~finish:(Lexing.lexeme_end_p lexbuf))) }

and read_single_line_comment =
  parse
  | newline { new_line lexbuf; read lexbuf }
  | eof { EOF }
  | _ { read_single_line_comment lexbuf }

and read_multi_line_comment =
  parse
  | '|' '#' { read lexbuf }
  | newline { new_line lexbuf; read_multi_line_comment lexbuf }
  | eof { raise (SyntaxError ("Unterminated comment", SourceBuilder.make ~start:(Lexing.lexeme_start_p lexbuf) ~finish:(Lexing.lexeme_end_p lexbuf))) }
  | _ { read_multi_line_comment lexbuf }

{
end
}
