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
          | "rec" -> REC
          | "in" -> IN
          | "fun" -> FUN
          | "true" -> TRUE
          | "false" -> FALSE
          | "int" -> INT  
          | "()" -> UNIT
          | id -> VAR id }
  | whitespace { read lexbuf }
  | eof { EOF }
  | '+' { ADD }
  | '-' { SUB }
  | '*' { MUL }
  | '/' { DIV }
  | '%' { MOD }
  | '<' { LT }
  | "<=" { LTE }
  | '>' { GT }
  | ">=" { GTE }
  | '=' { EQ }
  | "<>" { NEQ }
  | "&&" { AND }
  | "||" { OR }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | "->" { ARROW }
  | ':' { COLON }
  | _ { failwith "Unexpected character" }
