%{
open Utils
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
  | expr2 bop expr3 { Bop ($2, $1, $3) }
  | expr3 { $1 }

expr3:
  | expr3 expr3 { App ($1, $2) }
  | NUM { Num $1 }
  | VAR { Var $1 }
  | TRUE { True }
  | FALSE { False }
  | LPAREN expr RPAREN { $2 }

bop:
  | PLUS { Add }
  | MINUS { Sub }
  | MULT { Mul }
  | DIV { Div }
  | MOD { Mod }
  | LT { Lt }
  | LE { Lte }
  | GT { Gt }
  | GE { Gte }
  | EQ { Eq }
  | NEQ { Neq }
  | AND { And }
  | OR { Or }
