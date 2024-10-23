open Utils

let lex s =
  let words = split s in
  let rec helper words =
    match words with
    | [] -> Some []
    | h::t -> 
      match tok_of_string_opt h with
      | None -> None
      | Some tok -> 
        match helper t with
        | None -> None
        | Some tks -> Some (tok :: tks)
  in
  helper words
;;