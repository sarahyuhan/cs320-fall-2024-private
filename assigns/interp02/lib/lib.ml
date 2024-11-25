open Utils
open My_parser

let parse = My_parser.parse

let expr_of_value v =
  match v with
  | VFun (x, e) -> Fun (x, e)
  | VNum n -> Num n
  | VBool true -> True
  | VBool false -> False
  | VUnit -> Unit

let rec var_replace y x e = 
  match e with 
  | Num n -> Num n
  | True -> True
  | False -> False
  | Unit -> Unit
  | Var z -> if z = x then Var y else Var z
  | Bop (op, e1, e2) -> Bop (op, var_replace y x e1, var_replace y x e2)
  | If (e1, e2, e3) -> If (var_replace y x e1, var_replace y x e2, var_replace y x e3)
  | Let (z, e1, e2) -> if z = x then Let (z, var_replace y x e1, e2) else Let (z, var_replace y x e1, var_replace y x e2)
  | App (e1, e2) -> App (var_replace y x e1, var_replace y x e2)
  | Fun (z, e) -> if z = x then Fun (z, e) else Fun (z, var_replace y x e)

let rec subst value x expr =
  match expr with
  | Num n -> Num n
  | True -> True
  | False -> False
  | Unit -> Unit
  | Var y -> if x = y then (expr_of_value value) else Var y
  | Bop (op, e1, e2) -> Bop (op, subst value x e1, subst value x e2)
  | If (e1, e2, e3) -> If (subst value x e1, subst value x e2, subst value x e3)
  | Let (y, e1, e2) -> if x = y then Let (y, subst value x e1, e2) else Let (y, subst value x e1, subst value x e2)
  | App (e1, e2) -> App (subst value x e1, subst value x e2)
  | Fun (y, expr) ->
    if x = y
    then Fun (y, expr)
    else 
      let y' = gensym () in
      Fun (y', subst value x (var_replace y' y expr))
  

  let rec eval e =
    match e with
    | Num n -> Ok (VNum n)
    | True -> Ok (VBool true)
    | False -> Ok (VBool false)
    | Unit -> Ok VUnit
    | Var x -> Error (UnknownVar x)
    | Bop (op, e1, e2) -> (
      match op with
      | And -> (
            match eval e1 with
            | Ok (VBool false) -> Ok (VBool false) 
            | Ok (VBool true) -> eval e2           
            | Ok _ -> Error (InvalidArgs op)       
            | Error e -> Error e)
      | Or -> (
            match eval e1 with
            | Ok (VBool true) -> Ok (VBool true)
            | Ok (VBool false) -> eval e2
            | Ok _ -> Error (InvalidArgs op)
            | Error e -> Error e)
      | _ -> (
        match (eval e1, eval e2) with
        | Ok (VNum n1), Ok (VNum n2) -> (
          match op with
          | Add -> Ok (VNum (n1 + n2))
          | Sub -> Ok (VNum (n1 - n2))
          | Mul -> Ok (VNum (n1 * n2))
          | Div -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 / n2))
          | Mod -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 mod n2))
          | Lt -> Ok (VBool (n1 < n2))
          | Lte -> Ok (VBool (n1 <= n2))
          | Gt -> Ok (VBool (n1 > n2))
          | Gte -> Ok (VBool (n1 >= n2))
          | Eq -> Ok (VBool (n1 = n2))
          | Neq -> Ok (VBool (n1 <> n2))
          | _ -> Error (InvalidArgs op))
      | Ok _, Ok _ -> Error (InvalidArgs op)    
      | Error e1, _ -> Error e1
      | _, Error e2 -> Error e2))
    | If (e1, e2, e3) -> (
      match eval e1 with
      | Ok (VBool true) -> eval e2
      | Ok (VBool false) -> eval e3
      | Ok _ -> Error InvalidIfCond
      | Error e -> Error e)
    | Let (x, e1, e2) -> (
      match eval e1 with
      | Ok v -> eval (subst v x e2)
      | Error e -> Error e)
    | Fun (x, e) -> Ok (VFun (x, e))  
    | App (e1, e2) -> (
      match eval e1 with
      | Ok (VFun (x, e)) -> (
        match eval e2 with
        | Ok v2 -> eval (subst v2 x e)
        | Error e -> Error e)
      | Ok _ -> Error InvalidApp  
      | Error e -> Error e)

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

let interp prog =
interp_expr [] prog