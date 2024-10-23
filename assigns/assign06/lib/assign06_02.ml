open Utils

let parse toks =
  let rec helper toks stack =
    match toks, stack with
    | [], [e] -> Some e
    | [], _ -> None
    | (TNum n)::rest, _ -> helper rest (Num n::stack)
    | TAdd::rest, (e1::e2::stack') -> helper rest (Add (e2, e1)::stack')
    | TLt::rest, (e1::e2::stack') -> helper rest (Lt (e2, e1)::stack')
    | TIte::rest, (e1::e2::e3::stack') -> helper rest (Ite (e3, e2, e1)::stack')
    | _ -> None
  in
  helper toks []
;;
