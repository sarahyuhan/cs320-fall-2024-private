%{
open Utils

let rec mk_app e es =
  match es with
  | [] -> e
  | x :: es -> mk_app (App (e, x)) es
%}

%token <int> NUM
%token <string> VAR
%token IF THEN ELSE LET IN FUN TRUE FALSE ARROW UNIT
%token PLUS MINUS MULT DIV MOD
%token LT LE GT GE EQ NEQ AND OR
%token LPAREN RPAREN EOF

%start <Utils.prog> prog

%right OR
%right AND
%left LT LE GT GE EQ NEQ
%left PLUS MINUS
%left MULT DIV MOD

%%

prog:
  | expr EOF { $1 }

expr:
  | IF expr THEN expr ELSE expr { If ($2, $4, $6) }
  | LET VAR EQ expr IN expr { Let ($2, $4, $6) }
  | FUN VAR ARROW expr { Fun ($2, $4) }
  | expr2 { $1 }

expr2:
  | expr2 PLUS expr3 { Bop (Add, $1, $3) }
  | expr2 MINUS expr3 { Bop (Sub, $1, $3) }
  | expr3 { $1 }

expr3:
  | expr3 MULT expr4 { Bop (Mul, $1, $3) }
  | expr3 DIV expr4 { Bop (Div, $1, $3) }
  | expr3 MOD expr4 { Bop (Mod, $1, $3) }
  | expr4 { $1 }

expr4:
  | expr4 LT expr5 { Bop (Lt, $1, $3) }
  | expr4 LE expr5 { Bop (Lte, $1, $3) }
  | expr4 GT expr5 { Bop (Gt, $1, $3) }
  | expr4 GE expr5 { Bop (Gte, $1, $3) }
  | expr4 EQ expr5 { Bop (Eq, $1, $3) }
  | expr4 NEQ expr5 { Bop (Neq, $1, $3) }
  | expr5 { $1 }

expr5:
  | expr5 AND expr6 { Bop (And, $1, $3) }
  | expr5 OR expr6 { Bop (Or, $1, $3) }
  | expr6 { $1 }

expr6:
  | expr6 expr7 { mk_app $1 [$2] }
  | expr7 { $1 }

expr7:
  | NUM { Num $1 }
  | VAR { Var $1 }
  | TRUE { True }
  | FALSE { False }
  | LPAREN expr RPAREN { $2 }
