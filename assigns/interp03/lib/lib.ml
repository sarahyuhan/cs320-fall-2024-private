open Utils
include My_parser

let rec assoc_opt x = function
  | [] -> None
  | (y, v) :: rest -> if x = y then Some v else assoc_opt x rest

let rec list_exists f = function
  | [] -> false
  | x :: xs -> f x || list_exists f xs

type substitution = (ident * ty) list

let rec apply_subst_ty (subst : substitution) (ty : ty) : ty =
  match ty with
  | TUnit | TInt | TFloat | TBool -> ty
  | TVar var -> (match assoc_opt var subst with Some ty' -> ty' | None -> ty)
  | TList t -> TList (apply_subst_ty subst t)
  | TOption t -> TOption (apply_subst_ty subst t)
  | TPair (t1, t2) -> TPair (apply_subst_ty subst t1, apply_subst_ty subst t2)
  | TFun (arg_ty, ret_ty) -> TFun (apply_subst_ty subst arg_ty, apply_subst_ty subst ret_ty)

let compose_subst (subst1 : substitution) (subst2 : substitution) : substitution =
  let updated_subst2 = List.map (fun (x, t) -> (x, apply_subst_ty subst1 t)) subst2 in
  let merged = List.fold_left (fun acc (x, t) ->
      if list_exists (fun (y, _) -> x = y) acc then acc else (x, t) :: acc
    ) updated_subst2 subst1
  in
  merged

let rec freetype = function
  | TUnit | TInt | TFloat | TBool -> []
  | TVar x -> [x]
  | TList t | TOption t -> freetype t
  | TPair (t1, t2) | TFun (t1, t2) -> freetype t1 @ freetype t2

let ftv_scheme (Forall (vars, ty)) =
  List.filter (fun v -> not (List.mem v vars)) (freetype ty)

let ftv_env (env : stc_env) =
  List.fold_left (fun acc (_, scheme) -> acc @ ftv_scheme scheme) [] (Env.to_list env)

let generalize (env : stc_env) (ty : ty) : ty_scheme =
  let env_free_vars = ftv_env env in
  let ty_free_vars = freetype ty in
  let generalized_vars = List.filter (fun v -> not (List.mem v env_free_vars)) ty_free_vars in
  Forall (generalized_vars, ty)

let rec ty_subst (replacement : ty) (var : ident) (ty : ty) : ty =
  match ty with
  | TUnit | TInt | TFloat | TBool -> ty
  | TVar x -> if x = var then replacement else TVar x
  | TList t -> TList (ty_subst replacement var t)
  | TOption t -> TOption (ty_subst replacement var t)
  | TPair (t1, t2) -> TPair (ty_subst replacement var t1, ty_subst replacement var t2)
  | TFun (t1, t2) -> TFun (ty_subst replacement var t1, ty_subst replacement var t2)

let instantiate (Forall (vars, ty)) =
  let subst = List.map (fun var -> (var, TVar (gensym ()))) vars in
  apply_subst_ty subst ty

let rec unify_constraints = function
  | [] -> Some []
  | (t1, t2) :: rest when t1 = t2 -> unify_constraints rest
  | (TVar x, ty) :: rest | (ty, TVar x) :: rest ->
      if List.mem x (freetype ty) then None
      else
        let rest' = List.map (fun (t1, t2) -> (ty_subst ty x t1, ty_subst ty x t2)) rest in
        Option.map (fun sol -> (x, ty) :: sol) (unify_constraints rest')
  | (TFun (t1, t2), TFun (t3, t4)) :: rest ->
      unify_constraints ((t1, t3) :: (t2, t4) :: rest)
  | (TPair (t1, t2), TPair (t3, t4)) :: rest ->
      unify_constraints ((t1, t3) :: (t2, t4) :: rest)
  | (TList t1, TList t2) :: rest -> unify_constraints ((t1, t2) :: rest)
  | (TOption t1, TOption t2) :: rest -> unify_constraints ((t1, t2) :: rest)
  | _ -> None

let unify (initial_ty : ty) (constraints : constr list) : ty_scheme option =
  match unify_constraints constraints with
  | None -> None
  | Some subst ->
      let unified_ty = apply_subst_ty subst initial_ty in
      let free_vars = freetype unified_ty in
      Some (Forall (free_vars, unified_ty))

let rec infer_expr (env : stc_env) (e : expr) : ty * constr list =
  let fresh_ty () = TVar (gensym ()) in
  match e with
  | Unit -> (TUnit, [])
  | True | False -> (TBool, [])
  | Int _ -> (TInt, [])
  | Float _ -> (TFloat, [])
  | Var x -> (
      match Env.find_opt x env with
      | Some scheme -> (instantiate scheme, [])
      | None -> failwith ("Unbound variable: " ^ x)
    )
  | Fun (arg, ann, body) ->
      let arg_ty = match ann with Some t -> t | None -> fresh_ty () in
      let env' = Env.add arg (Forall ([], arg_ty)) env in
      let body_ty, body_constraints = infer_expr env' body in
      (TFun (arg_ty, body_ty), body_constraints)
  | App (e1, e2) ->
      let t1, c1 = infer_expr env e1 in
      let t2, c2 = infer_expr env e2 in
      let ret_ty = fresh_ty () in
      (ret_ty, (t1, TFun (t2, ret_ty)) :: c1 @ c2)
  | Let { is_rec; name; value; body } ->
      if not is_rec then
        let value_ty, value_constraints = infer_expr env value in
        let env' = Env.add name (Forall ([], value_ty)) env in
        let body_ty, body_constraints = infer_expr env' body in
        (body_ty, value_constraints @ body_constraints)
      else
        let fn_ty = fresh_ty () in
        let env' = Env.add name (Forall ([], fn_ty)) env in
        let value_ty, value_constraints = infer_expr env' value in
        let body_ty, body_constraints = infer_expr env' body in
        (body_ty, (fn_ty, value_ty) :: value_constraints @ body_constraints)
  | _ -> failwith "Expression not implemented yet"

let type_of (env : stc_env) (e : expr) : ty_scheme option =
  let ty, constraints = infer_expr env e in
  unify ty constraints

  

exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals


let rec eval_expr (env: dyn_env) (e: expr) : value =
  match e with
  | Unit -> 
    VUnit
  | True -> 
    VBool true
  | False -> VBool false
  | Int n -> VInt n
  | Float f -> VFloat f
  | Nil -> VList []
  | ENone -> VNone
  | ESome e ->
    let v = eval_expr env e in
    VSome v
  | Var x ->
    (match Env.find_opt x env with
     | Some v -> v
     | None -> failwith ("Runtime error: unbound variable "^x))
  | Annot (e, _) ->
    eval_expr env e
  | Assert e ->
    let v = eval_expr env e in
    (match v with
     | VBool true -> VUnit
     | VBool false -> raise AssertFail
     | _ -> raise AssertFail)
  | Bop (op, e1, e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    let int_op f = (match v1,v2 with
        | VInt x, VInt y -> f x y
        | _ -> raise CompareFunVals) in
    let float_op f = (match v1,v2 with
        | VFloat x, VFloat y -> f x y
        | _ -> raise CompareFunVals) in
    let bool_op f = (match v1,v2 with
        | VBool x, VBool y -> f x y
        | _ -> raise CompareFunVals) in
    let compare_op cmp =
      let rec cmp_val v1 v2 =
        match v1, v2 with
        | VUnit, VUnit -> 0
        | VBool x, VBool y -> compare x y
        | VInt x, VInt y -> compare x y
        | VFloat x, VFloat y -> compare x y
        | VList l1, VList l2 ->
          let rec cmp_list l1 l2 =
            match l1, l2 with
            | [], [] -> 0
            | [], _ -> -1
            | _, [] -> 1
            | x::xs, y::ys ->
              let c = cmp_val x y in
              if c <> 0 then c else cmp_list xs ys
          in cmp_list l1 l2
        | VNone, VNone -> 0
        | VSome x, VSome y -> cmp_val x y
        | VPair (a,b), VPair(c,d) ->
          let c1 = cmp_val a c in
          if c1 <> 0 then c1 else cmp_val b d
        | VClos _, _ | _, VClos _ -> raise CompareFunVals
        | _ ->
          let tag v = match v with
            | VUnit->0|VBool _->1|VInt _->2|VFloat _->3
            | VList _->4|VNone->5|VSome _->6|VPair _->7|VClos _->8
          in compare (tag v1) (tag v2)
      in
      let c = cmp_val v1 v2 in
      cmp c
    in
    (match op with
     | Add -> VInt (int_op ( + ))
     | Sub -> VInt (int_op ( - ))
     | Mul -> VInt (int_op ( * ))
     | Div ->
       (match v1,v2 with
        | VInt _, VInt 0 -> raise DivByZero
        | VInt x, VInt y -> VInt (x / y)
        | _ -> raise CompareFunVals)
     | Mod ->
       (match v1,v2 with
        | VInt _, VInt 0 -> raise DivByZero
        | VInt x, VInt y -> VInt (x mod y)
        | _ -> raise CompareFunVals)
     | AddF -> VFloat (float_op ( +. ))
     | SubF -> VFloat (float_op ( -. ))
     | MulF -> VFloat (float_op ( *. ))
     | DivF ->
       (match v1,v2 with
        | VFloat x, VFloat y ->
          if y = 0.0 then raise DivByZero else VFloat (x /. y)
        | _ -> raise CompareFunVals)
     | PowF ->
       (match v1,v2 with
        | VFloat x, VFloat y -> VFloat (x ** y)
        | _ -> raise CompareFunVals)
     | Cons ->
       (match v1,v2 with
        | v, VList vs -> VList (v::vs)
        | _ -> raise CompareFunVals)
     | Concat ->
       (match v1,v2 with
        | VList l1, VList l2 -> VList (l1 @ l2)
        | _ -> raise CompareFunVals)
     | Lt -> VBool (compare_op (fun c -> c<0))
     | Lte -> VBool (compare_op (fun c -> c<=0))
     | Gt -> VBool (compare_op (fun c -> c>0))
     | Gte -> VBool (compare_op (fun c -> c>=0))
     | Eq -> VBool (compare_op (fun c -> c=0))
     | Neq -> VBool (compare_op (fun c -> c<>0))
     | And -> VBool (bool_op (&&))
     | Or -> VBool (bool_op (||))
     | Comma ->
       VPair(v1,v2)
    )
  | If (e1,e2,e3) ->
    let v1 = eval_expr env e1 in
    (match v1 with
     | VBool true -> eval_expr env e2
     | VBool false -> eval_expr env e3
     | _ -> failwith "if condition not a boolean")
  | Fun (x,_,body) ->
    VClos {name=None;arg=x;body;env}
  | App (Var "length", e2) ->
    let v2 = eval_expr env e2 in
    (match v2 with
      | VList l -> VInt (List.length l)
      | _ -> failwith "Runtime error: length expects a list")

  | App (e1, e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1 with
      | VClos {arg; body; env=clos_env; name=_} ->
          let env' = Env.add arg v2 clos_env in
          eval_expr env' body
      | _ -> 
          (* Additional handling for built-in functions *)
          (match e1 with
          | Var fname ->
              (match Env.find_opt fname env with
                | Some (VClos closure) -> 
                    let env' = Env.add closure.arg v2 closure.env in
                    eval_expr env' closure.body
                | Some _ -> failwith ("Cannot apply non-function value: " ^ fname)
                | None -> failwith ("Unbound function: " ^ fname))
          | _ -> failwith ("Cannot apply non-function value: " ^ 
                            (match v1 with 
                              | VInt _ -> "int"
                              | VBool _ -> "bool"
                              | _ -> "unknown"))))
  | Let {is_rec; name; value; body} ->
    if not is_rec then
      (* Non-recursive let: just bind the value after evaluation *)
      let v_val = eval_expr env value in
      let env' = Env.add name v_val env in
      eval_expr env' body
    else (
      let placeholder = VClos { name = Some name; arg = "__placeholder"; body = Unit; env = env } in
      let env' = Env.add name placeholder env in
      let v_val = eval_expr env' value in
      let v_val = match v_val with
        | VClos c -> VClos { name = Some name; arg = c.arg; body = c.body; env = env' }
        | _ -> v_val
      in
      let env'' = Env.add name v_val env' in
      eval_expr env'' body
    ) 
  | ListMatch {matched;hd_name;tl_name;cons_case;nil_case} ->
    let vm = eval_expr env matched in
    (match vm with
     | VList [] -> eval_expr env nil_case
     | VList (h::t) ->
       let env' = Env.add hd_name h (Env.add tl_name (VList t) env) in
       eval_expr env' cons_case
     | _ -> failwith "list match on non-list")
  | OptMatch {matched;some_name;some_case;none_case} ->
    let vm = eval_expr env matched in
    (match vm with
     | VNone -> eval_expr env none_case
     | VSome v ->
       let env' = Env.add some_name v env in
       eval_expr env' some_case
     | _ -> failwith "option match on non-option")
  | PairMatch {matched;fst_name;snd_name;case} ->
    let vm = eval_expr env matched in
    (match vm with
     | VPair (a,b) ->
       let env' = Env.add fst_name a (Env.add snd_name b env) in
       eval_expr env' case
     | _ -> failwith "pair match on non-pair")

let base_env =
  let alpha = TVar (gensym()) in
  Env.empty
  |> Env.add "length" (Forall([], TFun(TList alpha, TInt)))
    
let type_check =
  let rec go ctxt = function
    | [] -> Some (Forall ([], TUnit))
    | {is_rec;name;value} :: ls ->
      match type_of ctxt (Let {is_rec;name;value; body = Var name}) with
      | Some ty ->
        (match ls with
        | [] -> Some ty
        | _ ->
          let ctxt = Env.add name ty ctxt in
          go ctxt ls)
      | None -> None
  in fun prog -> go base_env prog

let length_body =
  Fun ("xs", None,
        ListMatch {
          matched = Var "xs";
          hd_name = "h"; tl_name = "t";
          cons_case = Bop (Add, Int 1, App (Var "length", Var "t"));
          nil_case = Int 0;
        }
)
let base_runtime_env =
  let rec_env_for_length = Env.empty in
  let length_clos = VClos {
    name = Some "length";
    arg = "xs";
    body = length_body;
    env = rec_env_for_length (* Pass the environment directly *)
  } in
  let rec_env_for_length = Env.add "length" length_clos rec_env_for_length in
  rec_env_for_length


let eval p =
  let rec nest = function
    | [] -> Unit
    | [{is_rec;name;value}] -> Let {is_rec;name;value;body = Var name}
    | {is_rec;name;value} :: ls -> Let {is_rec;name;value;body = nest ls}
  in eval_expr base_runtime_env (nest p)


let interp input =
  match parse input with
  | Some prog -> (
    match type_check prog with
    | Some ty -> Ok (eval prog, ty)
    | None -> Error TypeError
  )
  | None -> Error ParseError

