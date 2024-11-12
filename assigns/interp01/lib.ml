open Utils
open Parser

type env = (string * value) list

let rec lookup env x =
  match env with
  | [] -> Error (UnknownVar x)
  | (y, v) :: env' -> if x = y then Ok v else lookup env' x

let eval_bop op v1 v2 =
  match op, v1, v2 with
  | Add, VNum n1, VNum n2 -> Ok (VNum (n1 + n2))
  | Sub, VNum n1, VNum n2 -> Ok (VNum (n1 - n2))
  | Mul, VNum n1, VNum n2 -> Ok (VNum (n1 * n2))
  | Div, VNum n1, VNum n2 -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 / n2))
  | Mod, VNum n1, VNum n2 -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 mod n2))
  | Lt, VNum n1, VNum n2 -> Ok (VBool (n1 < n2))
  | Lte, VNum n1, VNum n2 -> Ok (VBool (n1 <= n2))
  | Gt, VNum n1, VNum n2 -> Ok (VBool (n1 > n2))
  | Gte, VNum n1, VNum n2 -> Ok (VBool (n1 >= n2))
  | Eq, VNum n1, VNum n2 -> Ok (VBool (n1 = n2))
  | Neq, VNum n1, VNum n2 -> Ok (VBool (n1 <> n2))
  | And, VBool b1, VBool b2 -> Ok (VBool (b1 && b2))
  | Or, VBool b1, VBool b2 -> Ok (VBool (b1 || b2))
  | _ -> Error (InvalidArgs op)

let rec interp_expr env = function
  | Num n -> Ok (VNum n)
  | Var x -> lookup env x
  | Unit -> Ok VUnit
  | True -> Ok (VBool true)
  | False -> Ok (VBool false)
  | Bop (op, e1, e2) ->
      interp_expr env e1 >>= fun v1 ->
      interp_expr env e2 >>= fun v2 ->
      eval_bop op v1 v2
  | If (e1, e2, e3) ->
      interp_expr env e1 >>= (function
      | VBool true -> interp_expr env e2
      | VBool false -> interp_expr env e3
      | _ -> Error InvalidIfCond)
  | Let (x, e1, e2) ->
      interp_expr env e1 >>= fun v1 ->
      interp_expr ((x, v1) :: env) e2
  | Fun (x, e) -> Ok (VFun (x, e))
  | App (e1, e2) ->
      interp_expr env e1 >>= (function
      | VFun (x, body) ->
          interp_expr env e2 >>= fun v2 ->
          interp_expr ((x, v2) :: env) body
      | _ -> Error InvalidApp)

let rec subst value var expr =
  match expr with
  | Num n -> Num n
  | True -> True
  | False -> False
  | Unit -> Unit
  | Var y -> if x = y then (expr_of_value value) else Var y
  | Bop (op, e1, e2) -> Bop (op, subst value var e1, subst value var e2)
  | If (e1, e2, e3) -> If (subst value var e1, subst value var e2, subst value var e3)
  | Let (y, e1, e2) -> if x = y then Let (y, subst value var e1, e2) else Let (y, subst value var e1, subst value var e2)
  | App (e1, e2) -> App (subst v x e1, subst value var e2)
  | Fun (y, expr) ->
    if x = y
    then Fun (y, expr)
    else 
      let y' = gensym () in
      Fun (y', subst value var (var_replace y' y expr))

let parse s = My_parser.parse s
  
let interp s =
  match parse s with
  | Some expr -> eval expr
  | None -> Error ParseFail