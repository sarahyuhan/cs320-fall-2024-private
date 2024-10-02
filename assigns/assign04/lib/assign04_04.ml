type ident = string

type ty' = 
| Int
| Bool

type expr =
  | True
  | False
  | Num of int
  | Or of expr * expr
  | Add of expr * expr
  | IfThenElse of expr * expr * expr

type expr' = 
  | True
  | False
  | Num of int
  | Var of ident
  | Let of ident * expr' * expr'
  | Add of expr' * expr'
  | Or of expr' * expr'
  | IfThenElse of expr' * expr' * expr'

type context = (ident * ty') list

let rec type_of' (ctx : context) (e : expr') : ty' option =
  match e with
  | True -> Some Bool
  | False -> Some Bool
  | Num _ -> Some Int
  | Var x -> List.assoc_opt x ctx
  | Add (e1, e2) -> (
      match (type_of' ctx e1, type_of' ctx e2) with
      | (Some Int, Some Int) -> Some Int
      | _ -> None
    )
  | Or (e1, e2) -> (
      match (type_of' ctx e1, type_of' ctx e2) with
      | (Some Bool, Some Bool) -> Some Bool
      | _ -> None
    )
  | IfThenElse (e1, e2, e3) -> (
      match type_of' ctx e1 with
      | Some Bool -> (
          match (type_of' ctx e2, type_of' ctx e3) with
          | (Some t2, Some t3) when t2 = t3 -> Some t2
          | _ -> None
        )
      | _ -> None
    )
  | Let (x, e1, e2) -> (
      match type_of' ctx e1 with
      | Some t1 -> type_of' ((x, t1) :: ctx) e2
      | None -> None
    )
