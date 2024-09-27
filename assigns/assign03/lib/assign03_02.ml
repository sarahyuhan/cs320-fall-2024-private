let gen_fib l k =
  let len = List.length l in

  let rec sum_list lst total =
    match lst with
    | [] -> total
    | h :: t -> sum_list t (total + h)
  in

  let rec helper index current =
    match current with
    | [] -> failwith "empty"
    | first_elem :: _ ->
      if index = k + 1 then
        first_elem
      else if index < len then
        helper (index + 1) (List.nth l index :: current)
      else
        let total = sum_list (List.take len current) 0 in
        helper (index + 1) (total :: current)
  in

  helper 0 l
;;