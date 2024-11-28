%{
open Utils

let rec mk_app e = function
  | [] -> e
  | x :: es -> mk_app (SApp (e, x)) es
%}

%token <int> NUM
%token <string> VAR
%token UNIT
%token TRUE
%token FALSE
%token INT
%token LPAREN
%token RPAREN
%token ADD
%token SUB
%token MUL
%token DIV
%token MOD
%token LT
%token LTE
%token GT
%token GTE
%token EQ
%token NEQ
%token AND
%token OR
%token IF
%token THEN
%token ELSE
%token LET
%token IN
%token FUN
%token ARROW
%token COLON
%token REC


%token EOF

%right OR
%right AND
%left LT LTE GT GTE EQ NEQ
%left ADD SUB
%left MUL DIV MOD

%start <Utils.prog> prog

%%

prog:
  | toplists EOF { $1 }

expr:
  | IF expr THEN expr ELSE expr { SIf ($2, $4, $6) }
  | LET VAR args COLON ty EQ expr IN expr {
      SLet { is_rec = false; name = $2; args = $3; ty = $5; value = $7; body = $9 }
    }
  | LET REC VAR args COLON ty EQ expr IN expr {
      SLet { is_rec = true; name = $3; args = $4; ty = $6; value = $8; body = $10 }
    }
  | FUN args ARROW expr {
      match $2 with
      | [] -> failwith "Fail"
      | a :: t -> SFun { arg = a; args = t; body = $4 }
    }
  | expr2 { $1 }

toplists:
  | toplist EOF { $1 }

toplist:
  | toplist toplist_item { $1 @ [$2] }
  | toplist_item { [$1] }

toplist_item:
  | LET VAR args COLON ty EQ expr { { is_rec = false; name = $2; args = $3; ty = $5; value = $7 } }
  | LET REC VAR args COLON ty EQ expr { { is_rec = true; name = $3; args = $4; ty = $6; value = $8 } }

args:
  | LPAREN VAR COLON ty RPAREN args { ($2, $4) :: $6 }
  | { [] }


%inline bop:
  | ADD { Add }
  | SUB { Sub }
  | MUL { Mul }
  | DIV { Div }
  | MOD { Mod }
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }
  | EQ { Eq }
  | NEQ { Neq }
  | AND { And }
  | OR { Or }

expr2:
  | expr3 bop_expr_tail { $2 }

bop_expr_tail:
  | op = bop e = expr3 rest = bop_expr_tail { SBop (op, e, rest) }
  | e = expr3 { e }


expr3:
  | UNIT { SUnit }
  | TRUE { STrue }
  | FALSE { SFalse }
  | n = NUM { SNum n }
  | x = VAR { SVar x }
  | LPAREN e = expr RPAREN { e }

ty:
  | primary_ty ARROW ty { FunTy ($1, $3) }
  | primary_ty { $1 }
primary_ty:
  | INT { IntTy }
  | UNIT { UnitTy }
  | LPAREN ty RPAREN { $2 }
