open Utils
include My_parser

let rec assoc_opt x = function
  | [] -> None
  | (y,v)::rest -> if y = x then Some v else assoc_opt x rest

let rec list_exists f = function
  | [] -> false
  | x :: xs -> f x || list_exists f xs

type substitution = (ident * ty) list

let rec apply_subst_ty (s: substitution) (t: ty) : ty =
  match t with
  | TUnit | TInt | TFloat | TBool -> t
  | TVar x ->
    (match assoc_opt x s with
     | Some t' -> t'
     | None -> t)
  | TList t' -> TList (apply_subst_ty s t')
  | TOption t' -> TOption (apply_subst_ty s t')
  | TPair (t1, t2) -> TPair (apply_subst_ty s t1, apply_subst_ty s t2)
  | TFun (t1, t2) -> TFun (apply_subst_ty s t1, apply_subst_ty s t2)

let compose_subst (s1: substitution) (s2: substitution) : substitution =
  let s2' = List.map (fun (x,t) -> (x, apply_subst_ty s1 t)) s2 in
  let without_dups =
    List.fold_left (fun acc (x,t) ->
        if list_exists (fun (y,_) -> y = x) acc then acc else (x,t)::acc)
      s2' s1
  in without_dups

let rec ftv_ty = function
  | TUnit | TInt | TFloat | TBool -> []
  | TVar x -> [x]
  | TList t -> ftv_ty t
  | TOption t -> ftv_ty t
  | TPair (t1, t2) -> (ftv_ty t1) @ (ftv_ty t2)
  | TFun (t1, t2) -> (ftv_ty t1) @ (ftv_ty t2)

(** Collect free type variables from a type scheme *)
let ftv_scheme (Forall (vars, t)) =
  List.filter (fun x -> not (List.mem x vars)) (ftv_ty t)

(** Collect free type variables from an environment *)
let ftv_env (env: stc_env) =
  List.fold_left (fun acc (_, scheme) -> (ftv_scheme scheme) @ acc) [] (Env.to_list env)

(** Generalize a type over the free variables not in the environment *)
let generalize (env: stc_env) (t: ty) : ty_scheme =
  let env_ftv = ftv_env env in
  let t_ftv = ftv_ty t in
  let vars = List.filter (fun x -> not (List.mem x env_ftv)) t_ftv in
  Forall (vars, t)

(** Unification algorithm *)
let rec unify_one (t1: ty) (t2: ty) : substitution option =
  let occurs_check x t =
    List.mem x (ftv_ty t)
  in
  match t1, t2 with
  | TUnit, TUnit -> Some []
  | TInt, TInt -> Some []
  | TFloat, TFloat -> Some []
  | TBool, TBool -> Some []
  | TVar x, TVar y when x = y -> Some []
  | TVar x, _ ->
    if occurs_check x t2 then None
    else Some [(x,t2)]
  | _, TVar x ->
    if occurs_check x t1 then None
    else Some [(x,t1)]
  | TList a, TList b -> unify_pair a b
  | TOption a, TOption b -> unify_pair a b
  | TPair (a1,a2), TPair (b1,b2) ->
    unify_pairs [(a1,b1);(a2,b2)]
  | TFun (a1,a2), TFun (b1,b2) ->
    unify_pairs [(a1,b1);(a2,b2)]
  | _ -> None

and unify_pair a b = unify_pairs [(a,b)]

and unify_pairs constrs =
  match constrs with
  | [] -> Some []
  | (t1,t2)::rest ->
    (match unify_one t1 t2 with
     | None -> None
     | Some s ->
       let rest' = List.map (fun (x,y) -> (apply_subst_ty s x, apply_subst_ty s y)) rest in
       (match unify_pairs rest' with
        | None -> None
        | Some s2 -> Some (compose_subst s s2)))

let unify (ty: ty) (cs: constr list) : ty_scheme option =
  match unify_pairs cs with
  | None -> None
  | Some s ->
    let t' = apply_subst_ty s ty in
    (* Generalize with empty env here: in practice, type_of will handle context. *)
    let free_vars = ftv_ty t' in
    let scheme = Forall (free_vars, t') in
    Some scheme

(** Instantiate a type scheme with fresh type variables *)
let instantiate (Forall (vars, t)) =
  let s = List.map (fun x -> (x, TVar (gensym ()))) vars in
  apply_subst_ty s t

type inference_state = {
  env: stc_env;
  constraints: constr list;
}

let add_constraint st c = { st with constraints = c :: st.constraints }

(** Inference: returns (type, constraints) *)
let rec infer_expr (st: inference_state) (e: expr) : ty * inference_state =
  match e with
  | Unit ->
    (TUnit, st)
  | True | False ->
    (TBool, st)
  | Int _ ->
    (TInt, st)
  | Float _ ->
    (TFloat, st)
  | Nil ->
    let alpha = TVar (gensym()) in
    (TList alpha, st)
  | ENone ->
    let alpha = TVar (gensym()) in
    (TOption alpha, st)
  | ESome e1 ->
    let (t1, st1) = infer_expr st e1 in
    (TOption t1, st1)
  | Var x ->
    (match Env.find_opt x st.env with
     | Some sch ->
       (instantiate sch, st)
     | None -> failwith ("Unbound variable: " ^ x))
  | Annot (e, t) ->
    let (t_e, st_e) = infer_expr st e in
    let st_e' = add_constraint st_e (t_e, t) in
    (t, st_e')
  | Bop (op, e1, e2) ->
    let (t1, st1) = infer_expr st e1 in
    let (t2, st2) = infer_expr st1 e2 in
    let st3 =
      match op with
      | Add | Sub | Mul | Div | Mod ->
        let st' = add_constraint st2 (t1, TInt) in
        add_constraint st' (t2, TInt)
      | AddF | SubF | MulF | DivF | PowF ->
        let st' = add_constraint st2 (t1, TFloat) in
        add_constraint st' (t2, TFloat)
      | Cons ->
        let st' = add_constraint st2 (t2, TList t1) in
        st'
      | Concat ->
        let alpha = TVar (gensym()) in
        let st' = add_constraint st2 (t1, TList alpha) in
        add_constraint st' (t2, TList alpha)
      | Lt | Lte | Gt | Gte | Eq | Neq ->
        let st'' = add_constraint st2 (t1, t2) in
        st''
      | And | Or ->
        let st' = add_constraint st2 (t1, TBool) in
        add_constraint st' (t2, TBool)
      | Comma ->
        st2
    in
    let result_ty =
      match op with
      | Add | Sub | Mul | Div | Mod -> TInt
      | AddF | SubF | MulF | DivF | PowF -> TFloat
      | Lt | Lte | Gt | Gte | Eq | Neq | And | Or -> TBool
      | Cons | Concat ->
        apply_subst_ty [] t2
      | Comma ->
        TPair (t1, t2)
    in
    (result_ty, st3)
  | If (e1, e2, e3) ->
    let (t1, st1) = infer_expr st e1 in
    let (t2, st2) = infer_expr st1 e2 in
    let (t3, st3) = infer_expr st2 e3 in
    let st4 = add_constraint st3 (t1, TBool) in
    let st5 = add_constraint st4 (t2, t3) in
    (t2, st5)
  | Fun (x, ann, body) ->
    let alpha = match ann with Some ty -> ty | None -> TVar (gensym()) in
    let env' = Env.add x (Forall([],alpha)) st.env in
    let st' = { st with env = env' } in
    let (t_body, st_body) = infer_expr st' body in
    (TFun(alpha, t_body), {st_body with env = st.env})
  | App (e1, e2) ->
    let (t1, st1) = infer_expr st e1 in
    let (t2, st2) = infer_expr st1 e2 in
    let alpha = TVar (gensym()) in
    let st3 = add_constraint st2 (t1, TFun(t2, alpha)) in
    (alpha, st3)
  | Let {is_rec; name; value; body} ->
    if not is_rec then (
      let (t_val, st_val) = infer_expr st value in
      let scheme = generalize st.env t_val in
      let env' = Env.add name scheme st_val.env in
      let st_body = {st_val with env = env'} in
      let (t_body, st_body2) = infer_expr st_body body in
      (t_body, {st_body2 with env=st.env})
    ) else (
      let alpha = TVar(gensym()) in
      let beta = TVar(gensym()) in
      let env' = Env.add name (Forall([], TFun(alpha,beta))) st.env in
      let st' = {st with env=env'} in
      let (t_val, st_val) = infer_expr st' value in
      let st_val2 = add_constraint st_val (t_val, TFun(alpha,beta)) in
      let scheme = generalize st_val2.env (apply_subst_ty [] t_val) in
      let env'' = Env.add name scheme st_val2.env in
      let st_body = {st_val2 with env=env''} in
      let (t_body, st_body2) = infer_expr st_body body in
      (t_body, {st_body2 with env=st.env})
    )
  | Assert e1 ->
    let (t1, st1) = infer_expr st e1 in
    let st2 = add_constraint st1 (t1, TBool) in
    (TUnit, st2)
  | ListMatch {matched;hd_name;tl_name;cons_case;nil_case} ->
    let (t_mat, st1) = infer_expr st matched in
    let alpha = TVar(gensym()) in
    let st2 = add_constraint st1 (t_mat, TList alpha) in
    let env_cons = Env.add hd_name (Forall([],alpha)) st2.env in
    let env_cons = Env.add tl_name (Forall([], TList alpha)) env_cons in
    let st_cons = {st2 with env = env_cons} in
    let (t_cons, st_cons2) = infer_expr st_cons cons_case in
    let (t_nil, st_nil) = infer_expr {st_cons2 with env = st2.env} nil_case in
    let st3 = add_constraint st_nil (t_cons, t_nil) in
    (t_cons, st3)
  | OptMatch {matched;some_name;some_case;none_case} ->
    let (t_mat, st1) = infer_expr st matched in
    let alpha = TVar(gensym()) in
    let st2 = add_constraint st1 (t_mat, TOption alpha) in
    let env_some = Env.add some_name (Forall([],alpha)) st2.env in
    let st_some = {st2 with env = env_some} in
    let (t_some, st_some2) = infer_expr st_some some_case in
    let (t_none, st_none) = infer_expr {st_some2 with env = st2.env} none_case in
    let st3 = add_constraint st_none (t_some, t_none) in
    (t_some, st3)
  | PairMatch {matched;fst_name;snd_name;case} ->
    let (t_mat, st1) = infer_expr st matched in
    let alpha = TVar(gensym()) in
    let beta = TVar(gensym()) in
    let st2 = add_constraint st1 (t_mat, TPair (alpha,beta)) in
    let env_pair = Env.add fst_name (Forall([],alpha)) st2.env in
    let env_pair = Env.add snd_name (Forall([],beta)) env_pair in
    let st_pair = {st2 with env=env_pair} in
    let (t_case, st_case) = infer_expr st_pair case in
    (t_case, {st_case with env=st.env})

let type_of (ctx: stc_env) (e: expr) : ty_scheme option =
  let (t, st') = infer_expr {env=ctx; constraints=[]} e in
  let cs = st'.constraints in
  match unify t cs with
  | None -> None
  | Some scheme -> Some scheme


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
       | VClos {arg; body; env=clos_env; _} ->
         let env' = Env.add arg v2 clos_env in
         eval_expr env' body
       | _ -> failwith "application to non-function")
  | Let {is_rec; name; value; body} ->
  let v_val = eval_expr env value in
  if not is_rec then
    (* Non-recursive let: just bind the value and continue *)
    let env' = Env.add name v_val env in
    eval_expr env' body
  else
    (* Recursive let: If it's a closure, update its name. Otherwise, just bind the value. *)
    let v_val =
      match v_val with
      | VClos c ->
          VClos { c with name = Some name }
      | _ ->
          (* Here we allow non-function recursive bindings. 
              This is unusual but will not raise an exception. *)
          v_val
    in
    let env' = Env.add name v_val env in
    eval_expr env' body
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

let rec_env_for_length = Env.empty
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
  Env.empty
  |> Env.add "length" (VClos {name=None; arg="xs"; body=length_body; env=rec_env_for_length})
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

