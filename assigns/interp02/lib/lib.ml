open Utils
open My_parser
exception AssertFail
exception DivByZero

let parse s =
  match My_parser.parse s with
  | Some e -> Ok e
  | None -> Error ParseErr

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
              | And | Or -> Error (OpTyErrR (op, IntTy, IntTy)))
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

  
let eval e =
  let rec go env e =
    match e with
    | Num n -> Ok (VNum n)
    | True -> Ok (VBool true)
    | False -> Ok (VBool false)
    | Unit -> Ok VUnit
    | Var x -> (
        match Env.find_opt x env with
        | Some v -> Ok v
        | None -> Error (UnknownVar x))
    | If (cond, e1, e2) -> (
        match go env cond with
        | Ok (VBool true) -> go env e1
        | Ok (VBool false) -> go env e2
        | Ok _ -> Error (IfCondTyErr BoolTy)
        | Error e -> Error e)
    | Bop (op, e1, e2) ->
        let v1 = go env e1 in
        let v2 = go env e2 in
        (match op, v1, v2 with
        | Add, Ok (VNum n1), Ok (VNum n2) -> Ok (VNum (n1 + n2))
        | Sub, Ok (VNum n1), Ok (VNum n2) -> Ok (VNum (n1 - n2))
        | Mul, Ok (VNum n1), Ok (VNum n2) -> Ok (VNum (n1 * n2))
        | Div, Ok (VNum n1), Ok (VNum n2) when n2 = 0 -> Error DivByZero
        | Div, Ok (VNum n1), Ok (VNum n2) -> Ok (VNum (n1 / n2))
        | Mod, Ok (VNum n1), Ok (VNum n2) when n2 = 0 -> Error DivByZero
        | Mod, Ok (VNum n1), Ok (VNum n2) -> Ok (VNum (n1 mod n2))
        | Lt, Ok (VNum n1), Ok (VNum n2) -> Ok (VBool (n1 < n2))
        | Lte, Ok (VNum n1), Ok (VNum n2) -> Ok (VBool (n1 <= n2))
        | Gt, Ok (VNum n1), Ok (VNum n2) -> Ok (VBool (n1 > n2))
        | Gte, Ok (VNum n1), Ok (VNum n2) -> Ok (VBool (n1 >= n2))
        | Eq, Ok (VNum n1), Ok (VNum n2) -> Ok (VBool (n1 = n2))
        | Neq, Ok (VNum n1), Ok (VNum n2) -> Ok (VBool (n1 <> n2))
        | And, Ok (VBool b1), Ok (VBool b2) -> Ok (VBool (b1 && b2))
        | Or, Ok (VBool b1), Ok (VBool b2) -> Ok (VBool (b1 || b2))
        | _, Error e, _ | _, _, Error e -> Error e
        | _ -> failwith "Invalid operation")
    | Fun (arg, ty, body) -> Ok (VClos { name = None; arg; body; env })
    | App (e1, e2) -> (
        match go env e1 with
        | Ok (VClos { arg; body; env = env' }) -> (
            match go env e2 with
            | Ok v -> go (Env.add arg v env') body
            | Error e -> Error e)
        | Ok _ -> Error (FunAppTyErr BoolTy)
        | Error e -> Error e)
    | Assert e1 -> (
        match go env e1 with
        | Ok (VBool true) -> Ok VUnit
        | Ok (VBool false) -> Error (AssertTyErr BoolTy)
        | Ok _ -> Error (AssertTyErr BoolTy)
        | Error e -> Error e)
    | Let { is_rec; name; ty = _; value; body } ->
      let v1 = go env value in
      (match v1 with
      | Ok v ->
          let env' = if is_rec then Env.add name v env else Env.add name v env in
          go env' body
      | Error e -> Error e)
  in
  go Env.empty e
  
  

  let interp str =
    match parse str with
    | Ok prog -> 
        let expr = desugar prog in
        (match type_of expr with
         | Ok _ -> eval expr
         | Error e -> Error e)
    | Error e -> Error e  
