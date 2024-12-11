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
                  instantiate (substitute_type fresh_t v t) vs
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


let eval_expr (env : dyn_env) (expr : expr) : value =
  let rec evaluate env expr =
    match expr with
    | Unit -> VUnit
    | True -> VBool true
    | False -> VBool false
    | Int n -> VInt n
    | Float f -> VFloat f
    | Nil -> VList []
    | ENone -> VNone
    | Var name -> Env.find name env
    | Fun (param, _, body) -> 
        VClos {name = None; arg = param; body; env}
    | App (func, arg) -> 
        let func_val = evaluate env func in
        let arg_val = evaluate env arg in
        (match func_val with
         | VClos {name = None; arg; body; env = func_env} ->
             evaluate (Env.add arg arg_val func_env) body
         | VClos {name = Some self; arg; body; env = func_env} ->
             let rec_env = Env.add self func_val func_env in
             evaluate (Env.add arg arg_val rec_env) body
         | _ -> failwith "Invalid function application")
    | Let {is_rec = false; name; value; body} -> 
        let value_val = evaluate env value in
        evaluate (Env.add name value_val env) body
    | Let {is_rec = true; name; value; body} ->
        let clos_val = evaluate env value in
        (match clos_val with
         | VClos {name = None; arg; body = fn_body; env = fn_env} ->
             let new_env = Env.add name (VClos {name = Some name; arg; body = fn_body; env = fn_env}) env in
             evaluate new_env body
         | VClos {name = Some _; _} -> raise RecWithoutArg
         | _ -> failwith "Invalid recursive let binding")
    | Bop (op, e1, e2) ->
        let val1 = evaluate env e1 in
        let val2 = evaluate env e2 in
        (match op with
         | Add | Sub | Mul | Div | Mod -> (
             match val1, val2 with
             | VInt n1, VInt n2 -> 
                 (match op with
                  | Add -> VInt (n1 + n2)
                  | Sub -> VInt (n1 - n2)
                  | Mul -> VInt (n1 * n2)
                  | Div -> if n2 = 0 then raise DivByZero else VInt (n1 / n2)
                  | Mod -> if n2 = 0 then raise DivByZero else VInt (n1 mod n2)
                  | _ -> failwith "Invalid arithmetic operation")
             | _ -> failwith "Expected integer operands")
         | AddF | SubF | MulF | DivF | PowF -> (
             match val1, val2 with
             | VFloat f1, VFloat f2 -> 
                 (match op with
                  | AddF -> VFloat (f1 +. f2)
                  | SubF -> VFloat (f1 -. f2)
                  | MulF -> VFloat (f1 *. f2)
                  | DivF -> VFloat (f1 /. f2)
                  | PowF -> VFloat (f1 ** f2)
                  | _ -> failwith "Invalid floating-point operation")
             | _ -> failwith "Expected float operands")
         | Lt | Lte | Gt | Gte | Eq | Neq ->
             (match val1, val2 with
              | VClos _, _ | _, VClos _ -> raise CompareFunVals
              | _ -> VBool (
                  match op with
                  | Lt -> val1 < val2
                  | Lte -> val1 <= val2
                  | Gt -> val1 > val2
                  | Gte -> val1 >= val2
                  | Eq -> val1 = val2
                  | Neq -> val1 <> val2
                  | _ -> failwith "Invalid comparison operation"))
         | Cons -> (
             match val2 with
             | VList lst -> VList (val1 :: lst)
             | _ -> failwith "Expected a list")
         | Concat -> (
             match val1, val2 with
             | VList lst1, VList lst2 -> VList (lst1 @ lst2)
             | _ -> failwith "Expected two lists")
         | And -> (
             match val1, val2 with
             | VBool false, _ -> VBool false
             | VBool true, v -> v
             | _ -> failwith "Invalid boolean operation")
         | Or -> (
             match val1, val2 with
             | VBool true, _ -> VBool true
             | VBool false, v -> v
             | _ -> failwith "Invalid boolean operation")
         | Comma -> VPair (val1, val2))
    | If (cond, then_branch, else_branch) ->
        (match evaluate env cond with
         | VBool true -> evaluate env then_branch
         | VBool false -> evaluate env else_branch
         | _ -> failwith "Expected boolean condition in if statement")
    | ListMatch {matched; hd_name; tl_name; cons_case; nil_case} -> 
        (match evaluate env matched with
         | VList [] -> evaluate env nil_case
         | VList (hd :: tl) ->
             let new_env = Env.add tl_name (VList tl) (Env.add hd_name hd env) in
             evaluate new_env cons_case
         | _ -> failwith "Invalid list pattern match")
    | OptMatch {matched; some_name; some_case; none_case} ->
        (match evaluate env matched with
         | VNone -> evaluate env none_case
         | VSome val_some -> evaluate (Env.add some_name val_some env) some_case
         | _ -> failwith "Invalid option pattern match")
    | PairMatch {matched; fst_name; snd_name; case} ->
        (match evaluate env matched with
         | VPair (fst, snd) ->
             let new_env = Env.add snd_name snd (Env.add fst_name fst env) in
             evaluate new_env case
         | _ -> failwith "Invalid pair pattern match")
    | ESome expr -> VSome (evaluate env expr)
    | Assert expr ->
        (match evaluate env expr with
         | VBool true -> VUnit
         | _ -> raise AssertFail)
    | Annot (expr, _) -> evaluate env expr
  in
  evaluate env expr


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
    env = rec_env_for_length
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

