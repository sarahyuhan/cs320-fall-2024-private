open Utils
open My_parser

let parse s =
  let lexbuf = Lexing.from_string s in
  try Some (Par.prog Lex.read (Lexing.from_string s))
  with _ -> None

let desugar prog =
  let rec desugar_ty toplets =
    match toplets with
    | [] -> Unit
    | toplet :: rest ->
        let func_ty =
          List.fold_right
            (fun (_, arg_ty) acc -> FunTy (arg_ty, acc))
            (match toplet.value with
              | SFun { arg; args; _ } -> (fst arg, snd arg) :: args
              | _ -> toplet.args)
            toplet.ty
        in
        let desugared_value =
          match toplet.value with
          | SFun { arg; args; body } ->
              List.fold_right
                (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
                ((fst arg, snd arg) :: args)
                (desugar_expr body)
          | _ ->
              List.fold_right
                (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
                toplet.args
                (desugar_expr toplet.value)
        in
        Let {
          is_rec = toplet.is_rec;
          name = toplet.name;
          ty = func_ty;
          value = desugared_value;
          body = desugar_ty rest;
        }

  and desugar_expr expr =
    match expr with
    | SUnit -> Unit
    | STrue -> True
    | SFalse -> False
    | SNum n -> Num n
    | SVar x -> Var x
    | SBop (op, e1, e2) ->
        Bop (op, desugar_expr e1, desugar_expr e2)
    | SIf (cond, e1, e2) ->
        If (desugar_expr cond, desugar_expr e1, desugar_expr e2)
    | SApp (e1, e2) ->
        App (desugar_expr e1, desugar_expr e2)
    | SFun { arg; args; body } ->
        List.fold_right
          (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
          ((fst arg, snd arg) :: args)
          (desugar_expr body)
    | SAssert e1 ->
        Assert (desugar_expr e1)
    | SLet { is_rec; name; args; ty; value; body } ->
        let func_ty =
          List.fold_right
            (fun (_, arg_ty) acc -> FunTy (arg_ty, acc))
            (match value with
              | SFun { arg; args; _ } -> (fst arg, snd arg) :: args
              | _ -> args)
            ty
        in
        let desugared_value =
          match value with
          | SFun { arg; args; body } ->
              List.fold_right
                (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
                ((fst arg, snd arg) :: args)
                (desugar_expr body)
          | _ ->
              List.fold_right
                (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
                args
                (desugar_expr value)
        in
        Let {
          is_rec;
          name;
          ty = func_ty;
          value = desugared_value;
          body = desugar_expr body;
        }

  in
  desugar_ty prog
        

let type_of e =
  let rec go env e =
    match e with
    | Unit -> Ok UnitTy
    | True -> Ok BoolTy
    | False -> Ok BoolTy
    | Num n -> Ok IntTy
    | Var x ->
        (match Env.find_opt x env with
          | Some t -> Ok t
          | None -> Error (UnknownVar x))
    | If (e1, e2, e3) ->
        (match go env e1 with
          | Ok BoolTy ->
              (match go env e2, go env e3 with
              | Ok t1, Ok t2 when t1 = t2 -> Ok t1
              | Ok t1, Ok t2 -> Error (IfTyErr (t1, t2))
              | Error e, _ | _, Error e -> Error e)
          | Ok t -> Error (IfCondTyErr t)
          | Error e -> Error e)
    | Bop (op, e1, e2) ->
        (match go env e1, go env e2 with
          | Ok IntTy, Ok IntTy ->
              (match op with
              | Add | Sub | Mul | Div | Mod -> Ok IntTy
              | Lt | Lte | Gt | Gte | Eq | Neq -> Ok BoolTy
              | And | Or -> Error (OpTyErr (op, IntTy, IntTy)))
          | Ok BoolTy, Ok BoolTy ->
              (match op with
              | And | Or -> Ok BoolTy
              | Eq | Neq -> Ok BoolTy
              | _ -> Error (OpTyErrR (op, BoolTy, BoolTy)))
          | Ok t1, Ok t2 -> Error (OpTyErrR (op, t1, t2))
          | Error e, _ | _, Error e -> Error e)
    | Fun (x, t1, e) ->
        let env' = Env.add x t1 env in
        (match go env' e with
          | Ok t2 -> Ok (FunTy (t1, t2))
          | Error e -> Error e)
    | App (e1, e2) ->
        (match go env e1, go env e2 with
          | Ok (FunTy (t1, t2)), Ok t3 when t1 = t3 -> Ok t2
          | Ok (FunTy (t1, _)), Ok t2 -> Error (FunArgTyErr (t1, t2))
          | Ok t, _ -> Error (FunAppTyErr t)
          | Error e, _ | _, Error e -> Error e)
    | Let { is_rec; name; ty; value; body } ->
        let env' = Env.add name ty env in
        let env'' = if is_rec then env' else env in
        (match go env'' value with
          | Ok t when t = ty -> go env' body
          | Ok t -> Error (LetTyErr (ty, t))
          | Error e -> Error e)
    | Assert e ->
        (match go env e with
          | Ok BoolTy -> Ok UnitTy
          | Ok t -> Error (AssertTyErr t)
          | Error e -> Error e)
  in
  go Env.empty e        
  
let eval_bop op v1 v2 =
  match op, v1, v2 with
  | Add, VNum n1, VNum n2 -> Ok (VNum (n1 + n2))
  | Sub, VNum n1, VNum n2 -> Ok (VNum (n1 - n2))
  | Mul, VNum n1, VNum n2 -> Ok (VNum (n1 * n2))
  | Div, VNum n1, VNum n2 -> 
      if n2 = 0 then Error DivByZero else Ok (VNum (n1 / n2))
  | Mod, VNum n1, VNum n2 -> 
      if n2 = 0 then Error DivByZero else Ok (VNum (n1 mod n2))
  | Lt, VNum n1, VNum n2 -> Ok (VBool (n1 < n2))
  | Lte, VNum n1, VNum n2 -> Ok (VBool (n1 <= n2))
  | Gt, VNum n1, VNum n2 -> Ok (VBool (n1 > n2))
  | Gte, VNum n1, VNum n2 -> Ok (VBool (n1 >= n2))
  | Eq, VNum n1, VNum n2 -> Ok (VBool (n1 = n2))
  | Neq, VNum n1, VNum n2 -> Ok (VBool (n1 <> n2))
  | And, VBool b1, VBool b2 -> Ok (VBool (b1 && b2))
  | Or, VBool b1, VBool b2 -> Ok (VBool (b1 || b2))
  | _ -> Error (InvalidArgs op)


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
  | Let { is_rec; name = x; ty; value = e1; body = e2 } -> (
      match eval e1 with
      | Ok v1 -> eval (subst v1 x e2)
      | Error e -> Error e)
  | Fun (x, ty, body) -> Ok (VFun { name = None; arg = x; body = body; env = [] })
  | App (e1, e2) -> (
      match eval e1 with
      | Ok (VFun (x, body)) -> (
          match eval e2 with
          | Ok v2 -> eval (subst v2 x body)
          | Error e -> Error e)
      | Ok _ -> Error InvalidApp
      | Error e -> Error e)
  | Bop (op, e1, e2) -> (
    match eval e1, eval e2 with
    | Ok (VNum n1), Ok (VNum n2) -> eval_bop op (VNum n1) (VNum n2)
    | Ok (VBool b1), Ok (VBool b2) -> eval_bop op (VBool b1) (VBool b2)
    | Ok _, Ok _ -> Error (InvalidArgs op)
    | Error e, _ -> Error e
    | _, Error e -> Error e
)    
  | Assert e1 -> (
      match eval e1 with
      | Ok (VBool true) -> Ok VUnit
      | Ok (VBool false) -> Error (AssertTyErr BoolTy)
      | Ok _ -> Error (AssertTyErr BoolTy)
      | Error e -> Error e)
  

let interp str =
  match parse str with
  | Some prog ->
      let expr = desugar prog in
      (match type_of expr with
        | Ok _ -> Ok (eval expr)
        | Error e -> Error e)
  | None -> Error ParseErr