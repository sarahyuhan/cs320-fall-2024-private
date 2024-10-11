type ident = string

type ty = 
  | Unit
  | Arr of ty * ty

type expr = 
  | Var of ident
  | Fun of ident * ty * expr
  | App of expr * expr

type ctxt = (ident * ty) list

let rec lookup ctxt x =
  match ctxt with
  | [] -> None
  | (y, ty) :: rest -> if x = y then Some ty else lookup rest x

let rec type_of gamma expr =
  match expr with
  | Var x ->
      lookup gamma x
  | Fun (x, ty1, body) ->
      let gamma' = (x, ty1) :: gamma in
      (match type_of gamma' body with
       | Some ty2 -> Some (Arr (ty1, ty2))
       | None -> None)
  | App (e1, e2) ->
      (match type_of gamma e1 with
       | Some (Arr (ty1, ty2)) -> 
           (match type_of gamma e2 with
            | Some ty_arg when ty_arg = ty1 -> Some ty2
            | _ -> None)
       | _ -> None)
