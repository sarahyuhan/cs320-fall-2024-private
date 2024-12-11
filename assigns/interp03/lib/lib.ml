open Utils
include My_parser

let parse s : prog option = My_parser.parse s

let rec free_vars = function 
  | TUnit | TInt | TFloat | TBool -> VarSet.empty
  | TVar x -> VarSet.of_list [x]
  | TFun (t1, t2) -> VarSet.union (free_vars t1) (free_vars t2)
  | TList t -> free_vars t
  | TOption t -> free_vars t
  | TPair (t1, t2) -> VarSet.union (free_vars t1) (free_vars t2)

let occurs_in x ty = VarSet.mem x (free_vars ty)

let rec substitute_type ty var = function
  | TUnit -> TUnit
  | TInt -> TInt
  | TFloat -> TFloat
  | TBool -> TBool
  | TVar y -> if y = var then ty else TVar y
  | TFun (t1, t2) -> TFun (substitute_type ty var t1, substitute_type ty var t2)
  | TList t -> TList (substitute_type ty var t)
  | TOption t -> TOption (substitute_type ty var t)
  | TPair (t1, t2) -> TPair (substitute_type ty var t1, substitute_type ty var t2)

let apply_substitution subst ty =
  List.fold_left (fun ty' (var, u) -> substitute_type u var ty') ty subst

let apply_substitution_to_constraints subst constraints =
  List.map (fun (t1, t2) ->
    (apply_substitution subst t1, apply_substitution subst t2)
  ) constraints

let unify (target_ty : ty) (constraints : constr list) : ty_scheme option =
  let rec resolve_constraints constraints =
    match constraints with
    | [] -> Some []
    | (t1, t2) :: rest when t1 = t2 -> resolve_constraints rest
    | (TFun (a1, a2), TFun (b1, b2)) :: rest ->
      resolve_constraints ((a1, b1) :: (a2, b2) :: rest)
    | (TPair (a1, a2), TPair (b1, b2)) :: rest ->
      resolve_constraints ((a1, b1) :: (a2, b2) :: rest)
    | (TList a, TList b) :: rest ->
      resolve_constraints ((a, b) :: rest)
    | (TOption a, TOption b) :: rest ->
      resolve_constraints ((a, b) :: rest)
    | (TVar x, t) :: rest ->
      if occurs_in x t then None
      else
        let updated_constraints = apply_substitution_to_constraints [(x, t)] rest in
        (match resolve_constraints updated_constraints with
         | None -> None
         | Some solution -> Some ((x, t) :: solution))
    | (t, TVar x) :: rest ->
      if occurs_in x t then None
      else
        let updated_constraints = apply_substitution_to_constraints [(x, t)] rest in
        (match resolve_constraints updated_constraints with
         | None -> None
         | Some solution -> Some ((x, t) :: solution))
    | _ -> None
  in
  match resolve_constraints constraints with
  | None -> None
  | Some solution ->
      let final_type = apply_substitution solution target_ty in
      let vars = free_vars final_type in
      Some (Forall (VarSet.to_list vars, final_type))


let type_of (ctxt : stc_env) (e : expr) : ty_scheme option =
  let fresh () = TVar (gensym ()) in
  
  let rec generate_constraints e =
    match e with
    | Unit -> (TUnit, [])
    | True | False -> (TBool, [])
    | Int _ -> (TInt, [])
    | Float _ -> (TFloat, [])
    | Var x -> (
        match Env.find_opt x ctxt with
        | Some (Forall (bnd_vars, t)) ->
            let rec instantiate t vars =
              match vars with
              | [] -> t
              | v :: vs ->
                  let fresh_t = fresh () in
                  instantiate (ty_subst fresh_t v t) vs
            in
            (instantiate t bnd_vars, [])
        | None -> (fresh (), [])
      )
    | Fun (x, annot, body) ->
        let arg_ty = match annot with Some t -> t | None -> fresh () in
        let ctxt' = Env.add x (Forall ([], arg_ty)) ctxt in
        let (body_ty, constraints) = generate_constraints body in
        (TFun (arg_ty, body_ty), constraints)
    | App (e1, e2) ->
        let (t1, c1) = generate_constraints e1 in
        let (t2, c2) = generate_constraints e2 in
        let ret_ty = fresh () in
        (ret_ty, (t1, TFun (t2, ret_ty)) :: c1 @ c2)
    | ENone -> (TOption (fresh ()), [])
    | ESome e1 ->
        let (t, constraints) = generate_constraints e1 in
        (TOption t, constraints)
    | Nil -> (TList (fresh ()), [])
    | Bop (op, e1, e2) ->
        let (t1, c1) = generate_constraints e1 in
        let (t2, c2) = generate_constraints e2 in
        (match op with
          | Add | Sub | Mul | Div | Mod -> (TInt, (t1, TInt) :: (t2, TInt) :: c1 @ c2)
          | AddF | SubF | MulF | DivF | PowF -> (TFloat, (t1, TFloat) :: (t2, TFloat) :: c1 @ c2)
          | Lt | Lte | Gt | Gte | Eq | Neq -> (TBool, (t1, t2) :: c1 @ c2)
          | And | Or -> (TBool, (t1, TBool) :: (t2, TBool) :: c1 @ c2)
          | Cons ->
              let list_ty = TList t1 in
              (list_ty, (t2, list_ty) :: c1 @ c2)
          | Concat ->
              let elem_ty = fresh () in
              let list_ty = TList elem_ty in
              (list_ty, (t1, list_ty) :: (t2, list_ty) :: c1 @ c2)
          | Comma -> (TPair (t1, t2), c1 @ c2))
    | If (e1, e2, e3) ->
        let (t1, c1) = generate_constraints e1 in
        let (t2, c2) = generate_constraints e2 in
        let (t3, c3) = generate_constraints e3 in
        (t2, (t1, TBool) :: (t2, t3) :: c1 @ c2 @ c3)
    | Assert e1 -> (
        match e1 with
        | False -> (fresh (), [])
        | _ ->
            let (t, constraints) = generate_constraints e1 in
            (TUnit, (t, TBool) :: constraints))
    | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
        let (tm, cm) = generate_constraints matched in
        let (tn, cn) = generate_constraints nil_case in
        let alpha = fresh () in
        let ctxt' =
          Env.add tl_name (Forall ([], TList alpha))
          @@ Env.add hd_name (Forall ([], alpha)) ctxt
        in
        let (tc, cc) = generate_constraints cons_case in
        (tc, (tm, TList alpha) :: (tn, tc) :: cm @ cn @ cc)
    | OptMatch { matched; some_name; some_case; none_case } ->
        let (tm, cm) = generate_constraints matched in
        let alpha = fresh () in
        let (tn, cn) = generate_constraints none_case in
        let ctxt' = Env.add some_name (Forall ([], alpha)) ctxt in
        let (ts, cs) = generate_constraints some_case in
        (ts, (tm, TOption alpha) :: (tn, ts) :: cm @ cn @ cs)
    | PairMatch { matched; fst_name; snd_name; case } ->
        let (tm, cm) = generate_constraints matched in
        let alpha = fresh () in
        let beta = fresh () in
        let ctxt' =
          Env.add snd_name (Forall ([], beta))
          @@ Env.add fst_name (Forall ([], alpha)) ctxt
        in
        let (tc, cc) = generate_constraints case in
        (tc, (tm, TPair (alpha, beta)) :: cm @ cc)
    | Let { is_rec = false; name; value; body } ->
        let (t1, c1) = generate_constraints value in
        let ctxt' = Env.add name (Forall ([], t1)) ctxt in
        let (t2, c2) = generate_constraints body in
        (t2, c1 @ c2)
    | Let { is_rec = true; name; value; body } ->
        let alpha = fresh () in
        let beta = fresh () in
        let fn_ty = TFun (alpha, beta) in
        let ctxt' = Env.add name (Forall ([], fn_ty)) ctxt in
        let (t1, c1) = generate_constraints value in
        let ctxt'' = Env.add name (Forall ([], t1)) ctxt in
        let (t2, c2) = generate_constraints body in
        (t2, (t1, fn_ty) :: c1 @ c2)
    | Annot (e, t) ->
        let (te, ce) = generate_constraints e in
        (te, (te, t) :: ce)
  in

  let (ty, constraints) = generate_constraints e in
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

