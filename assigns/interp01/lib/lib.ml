open Utils
open My_parser

let parse = My_parser.parse

let rec subst value x expr =
  match expr with
  | Num n -> Num n
  | True -> True
  | False -> False
  | Unit -> Unit
  | Var y -> if x = y then expr_of_value value else Var y
  | Bop (op, e1, e2) -> Bop (op, subst value x e1, subst value x e2)
  | If (e1, e2, e3) -> If (subst value x e1, subst value x e2, subst value x e3)
  | Let (y, e1, e2) ->
      if x = y then Let (y, subst value x e1, e2)
      else Let (y, subst value x e1, subst value x e2)
  | App (e1, e2) -> App (subst value x e1, subst value x e2)
  | Fun (y, body) ->
      if x = y then Fun (y, body)
      else
        let y' = gensym () in
        Fun (y', subst value x (var_replace y' y body))

and var_replace y x expr =
  match expr with
  | Num n -> Num n
  | True -> True
  | False -> False
  | Unit -> Unit
  | Var z -> if z = x then Var y else Var z
  | Bop (op, e1, e2) -> Bop (op, var_replace y x e1, var_replace y x e2)
  | If (e1, e2, e3) ->
      If (var_replace y x e1, var_replace y x e2, var_replace y x e3)
  | Let (z, e1, e2) ->
      if z = x then Let (z, var_replace y x e1, e2)
      else Let (z, var_replace y x e1, var_replace y x e2)
  | App (e1, e2) -> App (var_replace y x e1, var_replace y x e2)
  | Fun (z, body) ->
      if z = x then Fun (z, body) else Fun (z, var_replace y x body)

let rec eval expr =
  match expr with
  | Num n -> Ok (VNum n)
  | True -> Ok (VBool true)
  | False -> Ok (VBool false)
  | Unit -> Ok VUnit
  | Var x -> Error (UnknownVar x)
  | Bop (op, e1, e2) -> (
      match eval e1, eval e2 with
      | Ok (VNum n1), Ok (VNum n2) -> eval_bop op (VNum n1) (VNum n2)
      | Ok (VBool b1), Ok (VBool b2) -> eval_bop op (VBool b1) (VBool b2)
      | Ok _, Ok _ -> Error (InvalidArgs op)
      | Error e, _ -> Error e
      | _, Error e -> Error e)
  | If (cond, e1, e2) -> (
      match eval cond with
      | Ok (VBool true) -> eval e1
      | Ok (VBool false) -> eval e2
      | Ok _ -> Error InvalidIfCond
      | Error e -> Error e)
  | Let (x, e1, e2) -> (
      match eval e1 with
      | Ok v1 -> eval (subst v1 x e2)
      | Error e -> Error e)
  | Fun (x, body) -> Ok (VFun (x, body))
  | App (e1, e2) -> (
      match eval e1 with
      | Ok (VFun (x, body)) -> (
          match eval e2 with
          | Ok v2 -> eval (subst v2 x body)
          | Error e -> Error e)
      | Ok _ -> Error InvalidApp
      | Error e -> Error e)

let interp s =
  match parse s with
  | Some expr -> eval expr
  | None -> Error ParseFail