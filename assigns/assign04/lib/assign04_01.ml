let rec lifespan f s pred count =
  if pred (f s) then count
  else if f s = s then max_int
  else lifespan f (f s) pred (count + 1)

let last_function_standing funcs start pred =
  let rec find_max funcs current_max current_func has_tie =
    match funcs with
    | [] -> if has_tie then None else current_func
    | f :: rest ->
        let life = lifespan f start pred 0 in
        match current_max, current_func with
        | None, _ -> find_max rest (Some life) (Some f) false
        | Some max_life, Some _ ->
            if life > max_life then
              find_max rest (Some life) (Some f) false
            else if life = max_life then
              find_max rest current_max current_func true
            else
              find_max rest current_max current_func has_tie
        | _ -> None
  in
  match funcs with
  | [] -> None
  | _ -> find_max funcs None None false
;;
