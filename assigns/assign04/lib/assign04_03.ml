open Assign04_02

type value = 
| VNum of int
| VBool of bool


  let rec eval (e : Assign04_02.expr) : value =
  match e with
  | True -> VBool true
  | False -> VBool false
  | Num n -> VNum n
  | Add (e1, e2) -> (
      match eval e1, eval e2 with
      | VNum v1, VNum v2 -> VNum (v1 + v2)
      | _ -> failwith "Invalid"
    )
  | Or (e1, e2) -> (
      match eval e1, eval e2 with
      | VBool v1, VBool v2 -> VBool (v1 || v2)
      | _ -> failwith "Invalid"
    )
  | IfThenElse (e1, e2, e3) -> (
      match eval e1 with
      | VBool true -> eval e2
      | VBool false -> eval e3
      | _ -> failwith "Invalid"
    )
