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


let determine_type context expression =
  let generate_fresh_type () = TVar (gensym ()) in

  let rec gather_constraints context expression =
    match expression with
    | Unit -> (TUnit, [])
    | True | False -> (TBool, [])
    | Int _ -> (TInt, [])
    | Float _ -> (TFloat, [])
    | Nil -> 
        let fresh_type = generate_fresh_type () in
        (TList fresh_type, [])
    | ENone -> 
        let fresh_type = generate_fresh_type () in
        (TOption fresh_type, [])
    | Var variable -> (
        match Env.find_opt variable context with
        | Some (Forall (variables, typ)) ->
            let substitution = List.fold_left 
              (fun acc var -> Env.add var (generate_fresh_type ()) acc) 
              Env.empty 
              variables
            in
            let rec substitute typ = 
              match typ with 
              | TVar v -> (match Env.find_opt v substitution with 
                          | Some t -> substitute t 
                          | None -> typ)
              | TList t -> TList (substitute t)
              | TOption t -> TOption (substitute t)
              | TPair (t1, t2) -> TPair (substitute t1, substitute t2)
              | TFun (t1, t2) -> TFun (substitute t1, substitute t2)
              | _ -> typ
            in
            (substitute typ, [])
        | None -> failwith ("Undefined variable: " ^ variable)
      )
    | ESome sub_expr ->
        let (sub_expr_type, constraints) = gather_constraints context sub_expr in
        (TOption sub_expr_type, constraints)
    | Annot (sub_expr, annotation_type) ->
        let (inferred_type, constraints) = gather_constraints context sub_expr in
        (annotation_type, (inferred_type, annotation_type) :: constraints)
    | PairMatch { matched; fst_name; snd_name; case } ->
        let (matched_type, constraints1) = gather_constraints context matched in
        let type1 = generate_fresh_type () in
        let type2 = generate_fresh_type () in
        let updated_context = 
          Env.add fst_name (Forall ([], type1)) 
          @@ Env.add snd_name (Forall ([], type2)) context
        in
        let (case_type, constraints2) = gather_constraints updated_context case in
        (case_type, constraints1 @ constraints2 @ 
                  [(matched_type, TPair (type1, type2))])
    | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
        let (matched_type, constraints1) = gather_constraints context matched in
        let list_element_type = generate_fresh_type () in
        let updated_context = 
          Env.add hd_name (Forall ([], list_element_type)) 
          @@ Env.add tl_name (Forall ([], TList list_element_type)) context
        in
        let (cons_case_type, constraints2) = gather_constraints updated_context cons_case in
        let (nil_case_type, constraints3) = gather_constraints context nil_case in
        (nil_case_type, constraints1 @ constraints2 @ constraints3 @ 
                        [(matched_type, TList list_element_type); 
                          (cons_case_type, nil_case_type)])
    | OptMatch { matched; some_name; some_case; none_case } ->
        let (matched_type, constraints1) = gather_constraints context matched in
        let option_element_type = generate_fresh_type () in
        let updated_context = Env.add some_name (Forall ([], option_element_type)) context in
        let (some_case_type, constraints2) = gather_constraints updated_context some_case in
        let (none_case_type, constraints3) = gather_constraints context none_case in
        (none_case_type, constraints1 @ constraints2 @ constraints3 @ 
                        [(matched_type, TOption option_element_type); 
                          (some_case_type, none_case_type)])
    | Bop (operator, expr1, expr2) ->
        let (type1, constraints1) = gather_constraints context expr1 in
        let (type2, constraints2) = gather_constraints context expr2 in
        (match operator with
        | Add | Sub | Mul | Div | Mod ->
            (TInt, constraints1 @ constraints2 @ [(type1, TInt); (type2, TInt)])
        | AddF | SubF | MulF | DivF | PowF ->
            (TFloat, constraints1 @ constraints2 @ [(type1, TFloat); (type2, TFloat)])
        | Lt | Lte | Gt | Gte | Eq | Neq ->
            (TBool, constraints1 @ constraints2 @ [(type1, type2)])
        | And | Or ->
            (TBool, constraints1 @ constraints2 @ [(type1, TBool); (type2, TBool)])
        | Cons ->
            let element_type = generate_fresh_type () in
            (TList element_type, constraints1 @ constraints2 @ 
                                [(type2, TList element_type); 
                                  (type1, element_type)])
        | Concat ->
            let element_type = generate_fresh_type () in
            (TList element_type, constraints1 @ constraints2 @ 
                                [(type1, TList element_type); 
                                  (type2, TList element_type)])
        | Comma ->
            (TPair (type1, type2), constraints1 @ constraints2)
        )
    | Fun (arg_name, opt_type, body) ->
        let arg_type = match opt_type with 
          | Some t -> t 
          | None -> generate_fresh_type () 
        in
        let updated_context = Env.add arg_name (Forall ([], arg_type)) context in
        let (body_type, body_constraints) = gather_constraints updated_context body in
        (TFun (arg_type, body_type), body_constraints)
    | App (func_expr, arg_expr) ->
        let (func_type, constraints1) = gather_constraints context func_expr in
        let (arg_type, constraints2) = gather_constraints context arg_expr in
        let result_type = generate_fresh_type () in
        (result_type, constraints1 @ constraints2 @ [(func_type, TFun (arg_type, result_type))])
    | If (condition, then_expr, else_expr) ->
        let (condition_type, constraints1) = gather_constraints context condition in
        let (then_type, constraints2) = gather_constraints context then_expr in
        let (else_type, constraints3) = gather_constraints context else_expr in
        (then_type, constraints1 @ constraints2 @ constraints3 @ 
                    [(condition_type, TBool); (then_type, else_type)])
    | Assert assert_expr ->
        let (assert_type, constraints) = gather_constraints context assert_expr in
        (TUnit, constraints @ [(assert_type, TBool)])
    | Let { is_rec; name; value; body } -> 
        let (value_type, value_constraints) = 
          if is_rec then 
            let alpha = generate_fresh_type () in
            let beta = generate_fresh_type () in
            let updated_context = Env.add name (Forall ([], TFun (alpha, beta))) context in
            let (val_type, constraints) = gather_constraints updated_context value in
            (val_type, constraints @ [(val_type, TFun (alpha, beta))])
          else 
            gather_constraints context value 
        in
        let updated_context = Env.add name (Forall ([], value_type)) context in
        let (body_type, body_constraints) = gather_constraints updated_context body in
        (body_type, value_constraints @ body_constraints)
  in
  try 
    let (final_type, all_constraints) = gather_constraints context expression in
    unify final_type all_constraints
  with 
  | _ -> failwith "Type inference error"      


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

