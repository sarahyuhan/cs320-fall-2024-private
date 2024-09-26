let rec add key x result =
  match result with
  | [] -> [(key, x)]
  | (h, t) :: rest ->
      if h = key then
        (h, t + x) :: rest
      else
        (h, t) :: add key x rest

let rec mk_unique_keys alst =
  match alst with
  | [] -> []
  | (key, x) :: rest ->
      let final = mk_unique_keys rest in
      add key x final
;;
