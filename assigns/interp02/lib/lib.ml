open Utils

exception AssertFail
exception DivByZero

let parse (s : string) : prog option =
  My_parser.parse s

let desugar program =
  let rec desugar_ty top_defs =
    match top_defs with
    | [] -> Unit
    | top_def :: remaining_defs ->
      let function_type =
        List.fold_right
          (fun (_, param_type) acc_type -> FunTy(param_type, acc_type))
          (match top_def.value with
           | SFun { arg; args; _ } -> (fst arg, snd arg) :: args
           | _ -> top_def.args)
          top_def.ty
      in
      let desugared_value =
        match top_def.value with
        | SFun { arg; args; body } ->
          List.fold_right
            (fun (param_name, param_type) acc_expr -> Fun(param_name, param_type, acc_expr))
            ((fst arg, snd arg) :: args)
            (desugar_expression body)
        | _ ->
          List.fold_right
            (fun (param_name, param_type) acc_expr -> Fun(param_name, param_type, acc_expr))
            top_def.args
            (desugar_expression top_def.value)
      in
      Let {
        is_rec = top_def.is_rec;
        name = top_def.name;
        ty = function_type;
        value = desugared_value;
        body = desugar_ty remaining_defs
      }

  and desugar_expression expr =
    match expr with
    | SUnit -> Unit
    | STrue -> True
    | SFalse -> False
    | SNum n -> Num n
    | SVar x -> Var x
    | SBop (op, e1, e2) -> Bop(op, desugar_expression e1, desugar_expression e2)
    | SIf (e1, e2, e3) -> If(desugar_expression e1, desugar_expression e2, desugar_expression e3)
    | SAssert e -> Assert(desugar_expression e)
    | SApp (e1, e2) -> App(desugar_expression e1, desugar_expression e2)
    | SFun { arg; args; body } ->
      List.fold_right
        (fun (param_name, param_type) acc_expr -> Fun(param_name, param_type, acc_expr))
        ((fst arg, snd arg) :: args)
        (desugar_expression body)
    | SLet { is_rec; name; args; ty; value; body } ->
      let function_type =
        List.fold_right
          (fun (_, param_type) acc_type -> FunTy(param_type, acc_type))
          (match value with
           | SFun { arg; args; _ } -> (fst arg, snd arg) :: args
           | _ -> args)
          ty
      in
      let desugared_value =
        match value with
        | SFun { arg; args; body } ->
          List.fold_right
            (fun (param_name, param_type) acc_expr -> Fun(param_name, param_type, acc_expr))
            ((fst arg, snd arg) :: args)
            (desugar_expression body)
        | _ ->
          List.fold_right
            (fun (param_name, param_type) acc_expr -> Fun(param_name, param_type, acc_expr))
            args
            (desugar_expression value)
      in
      Let {
        is_rec;
        name;
        ty = function_type;
        value = desugared_value;
        body = desugar_expression body
      }
  in
  desugar_ty program

let type_of expr =
    let rec infer_type env expr =
    match expr with
    | Unit -> Ok UnitTy
    | Num _ -> Ok IntTy
    | True -> Ok BoolTy
    | False -> Ok BoolTy
    | Var x ->
        (match Env.find_opt x env with
        | Some t -> Ok t
        | None -> Error (UnknownVar x))
    | If (e1, e2, e3) ->
        (match infer_type env e1 with
        | Ok BoolTy ->
            (match infer_type env e2, infer_type env e3 with
                | Ok t1, Ok t2 when t1 = t2 -> Ok t1
                | Ok t1, Ok t2 -> Error (IfTyErr (t1, t2))
                | Error e, _ | _, Error e -> Error e)
        | Ok t -> Error (IfCondTyErr t)
        | Error e -> Error e)
    | Fun (x, t1, e) ->
        let env' = Env.add x t1 env in
        (match infer_type env' e with
        | Ok t2 -> Ok (FunTy (t1, t2))
        | Error e -> Error e)
    | App (e1, e2) ->
        (match infer_type env e1, infer_type env e2 with
        | Ok (FunTy (t1, t2)), Ok t3 when t1 = t3 -> Ok t2
        | Ok (FunTy (t1, _)), Ok t2 -> Error (FunArgTyErr (t1, t2))
        | Ok t, _ -> Error (FunAppTyErr t)
        | Error e, _ -> Error e)
    | Let { is_rec; name; ty; value; body } ->
        let env' = Env.add name ty env in
        let env'' = if is_rec then env' else env in
        (match infer_type env'' value with
        | Ok t when t = ty -> infer_type env' body
        | Ok t -> Error (LetTyErr (ty, t))
        | Error e -> Error e)
    | Bop (op, e1, e2) ->
        let ty1 = infer_type env e1 in
        let ty2 = infer_type env e2 in
        (match ty1, ty2 with
        | Error e, _ | _, Error e -> Error e
        | Ok t1, Ok t2 ->
            (match op with
                | Add | Sub | Mul | Div | Mod ->
                    if t1 = IntTy && t2 = IntTy then Ok IntTy
                    else if t1 <> IntTy then Error (OpTyErrL (op, IntTy, t1))
                    else Error (OpTyErrR (op, IntTy, t2))
                | Lt | Lte | Gt | Gte ->
                    if t1 = IntTy && t2 = IntTy then Ok BoolTy
                    else if t1 <> IntTy then Error (OpTyErrL (op, IntTy, t1))
                    else Error (OpTyErrR (op, IntTy, t2))
                | And | Or ->
                    if t1 = BoolTy && t2 = BoolTy then Ok BoolTy
                    else if t1 <> BoolTy then Error (OpTyErrL (op, BoolTy, t1))
                    else Error (OpTyErrR (op, BoolTy, t2))
                | Eq | Neq ->
                    if t1 = t2 then Ok BoolTy
                    else Error (OpTyErrR (op, t1, t2))))
    | Assert e ->
        (match infer_type env e with
        | Ok BoolTy -> Ok UnitTy
        | Ok t -> Error (AssertTyErr t)
        | Error e -> Error e)
    in infer_type Env.empty expr

let eval expr =
  let rec evaluate env expr =
    match expr with
    | Unit -> VUnit
    | True -> VBool true
    | False -> VBool false
    | Num n -> VNum n
    | Var x -> Env.find x env
    | If (e1, e2, e3) ->
      (match evaluate env e1 with
       | VBool true -> evaluate env e2
       | VBool false -> evaluate env e3
       | _ -> failwith "")
    | Bop (op, e1, e2) ->
      let v1 = evaluate env e1 in
      let v2 = evaluate env e2 in
      (match op, v1, v2 with
       | Add, VNum n1, VNum n2 -> VNum (n1 + n2)
       | Sub, VNum n1, VNum n2 -> VNum (n1 - n2)
       | Mul, VNum n1, VNum n2 -> VNum (n1 * n2)
       | Div, VNum n1, VNum n2 ->
         if n2 = 0 then raise DivByZero
         else VNum (n1 / n2)
       | Mod, VNum n1, VNum n2 ->
         if n2 = 0 then raise DivByZero
         else VNum (n1 mod n2)
       | Lt, VNum n1, VNum n2 -> VBool (n1 < n2)
       | Lte, VNum n1, VNum n2 -> VBool (n1 <= n2)
       | Gt, VNum n1, VNum n2 -> VBool (n1 > n2)
       | Gte, VNum n1, VNum n2 -> VBool (n1 >= n2)
       | Eq, VNum n1, VNum n2 -> VBool (n1 = n2)
       | Neq, VNum n1, VNum n2 -> VBool (n1 <> n2)
       | And, VBool b1, VBool b2 -> VBool (b1 && b2)
       | Or, VBool b1, VBool b2 -> VBool (b1 || b2)
       | _ -> failwith "")
    | Fun (arg, _, e) -> VClos { name = None; arg; body = e; env }
    | App (e1, e2) ->
      let v1 = evaluate env e1 in
      let v2 = evaluate env e2 in
      (match v1 with
       | VClos { name; arg; body; env = env' } ->
         let env'' = match name with
           | Some f -> Env.add f v1 env'
           | None -> env'
         in
         evaluate (Env.add arg v2 env'') body
       | _ -> failwith "")
    | Let { is_rec; name; ty = _; value; body } ->
      let v1 =
        if is_rec then
          match value with
          | Fun (arg, _, e) ->
            let rec_clos = VClos { name = Some name; arg; body = e; env = env } in
            let env' = Env.add name rec_clos env in
            VClos { name = Some name; arg; body = e; env = env' }
          | _ -> evaluate env value
        else evaluate env value
      in
      evaluate (Env.add name v1 env) body
    | Assert e ->
      (match evaluate env e with
       | VBool true -> VUnit
       | VBool false -> raise AssertFail
       | _ -> failwith "")
  in evaluate Env.empty expr

let interp (s : string) : (value, error) result =
  let handle_eval expr =
      match type_of expr with
      | Error e -> Error e
      | Ok _ -> 
          match eval expr with
          | v -> Ok v in
  match parse s with
  | None -> Error ParseErr
  | Some prog ->
      let expr = desugar prog in
      handle_eval expr
