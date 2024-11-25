open Utils
open My_parser

let parse = My_parser.parse

let desugar prog =
  let rec desugar_expr = function
    | Prog [] -> Unit
    | Prog (hd :: tl) -> 
        (match hd with
        | TopLet (x, args, ty, e) -> 
            Let (x, 
                 List.fold_right 
                   (fun (arg, ty) acc -> Fun (arg, acc)) 
                   args 
                   (desugar_expr e), 
                 desugar_expr (Prog tl))
        | TopLetRec (x, args, ty, e) -> 
            LetRec (x, 
                    List.fold_right 
                      (fun (arg, ty) acc -> Fun (arg, acc)) 
                      args 
                      (desugar_expr e), 
                    desugar_expr (Prog tl)))
  in
  desugar_expr prog

let type_of expr =
  let rec infer_type env = function
    | Num _ -> Ok TInt
    | True | False -> Ok TBool
    | Unit -> Ok TUnit
    | Var x -> 
        (match List.assoc_opt x env with
         | Some ty -> Ok ty
         | None -> Error (UnknownVar x))
    | Bop (op, e1, e2) -> 
        infer_type env e1 >>= fun t1 ->
        infer_type env e2 >>= fun t2 ->
        (match (op, t1, t2) with
         | (Add, TInt, TInt) | (Sub, TInt, TInt) | (Mul, TInt, TInt)
         | (Div, TInt, TInt) | (Mod, TInt, TInt) -> Ok TInt
         | (And, TBool, TBool) | (Or, TBool, TBool) -> Ok TBool
         | _ -> Error (OpTyErrR (op, t1, t2)))
    | If (cond, t1, t2) ->
        infer_type env cond >>= fun tcond ->
        (if tcond <> TBool then Error (IfCondTyErr tcond)
         else
           infer_type env t1 >>= fun tthen ->
           infer_type env t2 >>= fun telse ->
           if tthen = telse then Ok tthen
           else Error (IfTyErr (tthen, telse)))
    | Let (x, e1, e2) -> 
        infer_type env e1 >>= fun ty ->
        infer_type ((x, ty) :: env) e2
    | Fun (arg, body) -> 
        (match arg with
         | (x, t) -> infer_type ((x, t) :: env) body >>= fun tbody ->
                     Ok (TFun (t, tbody)))
    | App (f, arg) -> 
        infer_type env f >>= fun tf ->
        infer_type env arg >>= fun targ ->
        (match tf with
         | TFun (t1, t2) when t1 = targ -> Ok t2
         | TFun (t1, _) -> Error (FunArgTyErr (t1, targ))
         | _ -> Error (FunAppTyErr tf))
    | Assert e ->
        infer_type env e >>= fun t ->
        if t = TBool then Ok TUnit
        else Error (AssertTyErr t)
  in
  infer_type [] expr

let rec eval env = function
  | Num n -> VNum n
  | True -> VBool true
  | False -> VBool false
  | Unit -> VUnit
  | Var x -> List.assoc x env
  | Bop (op, e1, e2) -> 
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      eval_bop op v1 v2
  | If (cond, t1, t2) ->
      (match eval env cond with
       | VBool true -> eval env t1
       | VBool false -> eval env t2
       | _ -> raise (Failure "Invalid"))
  | Let (x, e1, e2) ->
      let v1 = eval env e1 in
      eval ((x, v1) :: env) e2
  | Fun (arg, body) -> VClosure (env, arg, body)
  | App (f, arg) ->
      let vf = eval env f in
      let va = eval env arg in
      (match vf with
       | VClosure (env', (x, _), body) ->
           eval ((x, va) :: env') body
       | _ -> raise (Failure "Invalid"))
  | Assert e ->
      (match eval env e with
       | VBool true -> VUnit
       | VBool false -> raise AssertFail
       | _ -> raise (Failure "Invalid"))

let interp s =
  match parse s with
  | Some prog ->
      let expr = desugar prog in
      (match type_of expr with
       | Ok _ -> Ok (eval [] expr)
       | Error err -> Error err)
  | None -> Error ParseFail