{
open Par
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule read =
  parse
  | num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | var { match Lexing.lexeme lexbuf with
          | "if" -> IF
          | "then" -> THEN
          | "else" -> ELSE
          | "let" -> LET
          | "in" -> IN
          | "fun" -> FUN
          | "true" -> TRUE
          | "false" -> FALSE
          | "()" -> UNIT
          | id -> VAR id }
  | whitespace { read lexbuf }
  | eof { EOF }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { MULT }
  | '/' { DIV }
  | '%' { MOD }
  | '<' { LT }
  | "<=" { LE }
  | '>' { GT }
  | ">=" { GE }
  | '=' { EQ }
  | "<>" { NEQ }
  | "&&" { AND }
  | "||" { OR }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | "->" { ARROW }
  | _ { failwith "Unexpected character" }