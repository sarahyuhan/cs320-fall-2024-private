open Utils

let parse s =
  match My_parser.parse s with
  | Some expr -> Ok expr
  | None -> Error ParseFail

let rec desugar (p : prog) : expr =
  match p with
  | Prog (toplets, _) ->
    List.fold_right (fun toplet acc -> desugar_toplet toplet acc) toplets Unit  


and desugar_toplet (toplet : toplet) (acc : expr) : expr =
  match toplet with
  | Let (x, args, ty, e) ->
    let func_expr = desugar_function args e in
    Let (x, func_expr, acc)
  | LetRec (f, args, ty, e) ->
    let func_expr = desugar_function args e in
    LetRec (f, func_expr, acc)

and desugar_function (args : (string * ty) list) (body : expr) : expr =
  List.fold_right
    (fun (arg, ty) acc -> Fun (arg, ty, acc))
    args
    (desugar_expr body)

and desugar_expr (e : expr) : expr =
  match e with
  | Let (x, args, ty, e1, e2) ->
    Let (x, desugar_function args e1, desugar_expr e2)
  | LetRec (f, args, ty, e1, e2) ->
    LetRec (f, desugar_function args e1, desugar_expr e2)
  | If (e1, e2, e3) ->
    If (desugar_expr e1, desugar_expr e2, desugar_expr e3)
  | Fun (args, body) ->
    desugar_function args body
  | App (e1, e2) ->
    App (desugar_expr e1, desugar_expr e2)
  | Bop (op, e1, e2) ->
    Bop (op, desugar_expr e1, desugar_expr e2)
  | Assert e -> Assert (desugar_expr e)
  | _ -> e

let rec type_of_expr (env : (string * ty) list) (e : expr) : (ty, error) result =
  match e with
  | Num _ -> Ok TInt
  | True | False -> Ok TBool
  | Unit -> Ok TUnit
  | Var x ->
    (match List.assoc_opt x env with
    | Some ty -> Ok ty
    | None -> Error (UnknownVar x))
  | If (cond, e1, e2) ->
    (match type_of_expr env cond with
    | Ok TBool -> (
        match (type_of_expr env e1, type_of_expr env e2) with
        | Ok ty1, Ok ty2 when ty1 = ty2 -> Ok ty1
        | Ok ty1, Ok ty2 -> Error (IfTyErr (ty1, ty2))
        | Error e, _ | _, Error e -> Error e)
    | Ok ty -> Error (IfCondTyErr ty)
    | Error e -> Error e)
  | Fun (arg, ty, body) ->
    let env' = (arg, ty) :: env in
    (match type_of_expr env' body with
    | Ok ty' -> Ok (TFun (ty, ty'))
    | Error e -> Error e)
  | App (e1, e2) ->
    (match type_of_expr env e1 with
    | Ok (TFun (ty_arg, ty_ret)) -> (
        match type_of_expr env e2 with
        | Ok ty when ty = ty_arg -> Ok ty_ret
        | Ok ty -> Error (FunArgTyErr (ty_arg, ty))
        | Error e -> Error e)
    | Ok ty -> Error (FunAppTyErr ty)
    | Error e -> Error e)
  | Bop (op, e1, e2) ->
    (* Check operator type *)
    (match type_of_operator op with
    | (ty_left, ty_right, ty_result) -> (
        match (type_of_expr env e1, type_of_expr env e2) with
        | Ok ty1, Ok ty2 when ty1 = ty_left && ty2 = ty_right -> Ok ty_result
        | Ok ty1, _ when ty1 <> ty_left -> Error (OpTyErrL (op, ty_left, ty1))
        | _, Ok ty2 when ty2 <> ty_right -> Error (OpTyErrR (op, ty_right, ty2))
        | Error e, _ | _, Error e -> Error e)
    | _ -> Error (InvalidArgs op))
  | _ -> Error ParseFail

and type_of_operator op =
  match op with
  | Add | Sub | Mul | Div | Mod -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte | Eq | Neq -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)


let type_of e =
  type_of_expr [] e

let rec eval_expr env = function
  | Num n -> VNum n
  | True -> VBool true
  | False -> VBool false
  | Unit -> VUnit
  | Var x -> List.assoc x env
  | If (cond, e1, e2) -> (
      match eval_expr env cond with
      | VBool true -> eval_expr env e1
      | VBool false -> eval_expr env e2
      | _ -> raise AssertFail)
  | Fun (arg, _, body) -> VClosure (env, arg, body)
  | App (e1, e2) -> (
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      match v1 with
      | VClosure (env', arg, body) -> eval_expr ((arg, v2) :: env') body
      | _ -> raise InvalidApp)
  | Bop (op, e1, e2) -> eval_bop op (eval_expr env e1) (eval_expr env e2)
  | Assert e -> (
      match eval_expr env e with
      | VBool true -> VUnit
      | _ -> raise AssertFail)
  | _ -> raise ParseFail


let eval e =
  try Ok (eval_expr [] e) with
  | AssertFail -> Error AssertFail
  | InvalidApp -> Error InvalidApp

(* Part 5: Interp *)
let interp s =
  match parse s with
  | Some prog -> (
      match type_of (desugar prog) with
      | Ok _ -> eval (desugar prog)
      | Error e -> Error e)
  | None -> Error ParseFail