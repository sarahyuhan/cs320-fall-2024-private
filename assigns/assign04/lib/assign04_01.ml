let rec lifespan f s pred count =
  if pred (f s) then count
  else lifespan f (f s) pred (count + 1)

let last_function_standing funcs start pred =
  let rec find_max funcs current_max current_func =
    match funcs with
    | [] -> current_func
    | f :: rest ->
        let life = lifespan f start pred 0 in
        match current_max, current_func with
        | None, _ -> find_max rest (Some life) (Some f)
        | Some max_life, Some max_func ->
            if life > max_life then
              find_max rest (Some life) (Some f)
            else if life = max_life then
              None
            else
              find_max rest (Some max_life) (Some max_func)
        | _ -> None
  in
  find_max funcs None None
;;

