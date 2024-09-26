let rec reverse lst =
  match lst with
  | [] -> []
  | h :: t -> (reverse t) @ [h]


let valid lst =
  let rec check lst previous =
    match lst with
    | [] -> true
    | [x] -> x <> 0
    | x1 :: x2 :: rest ->
        if x1 = 0 then false
        else if x2 = 0 then 
          if previous * x1 > 0 then false
          else check rest 0 
        else if x1 * x2 < 0 then false
        else check (x2 :: rest) x1
  in
  match lst with
  | [] -> true
  | x :: xs -> check xs x

let rec grouper lst current acc =
  match lst with
  | [] -> reverse (reverse current :: acc)
  | 0 :: rest -> grouper rest [] (reverse current :: acc)
  | x :: rest when current = [] || (match current with y::_ -> (x * y) > 0 | _ -> false) ->
      grouper rest (x :: current) acc
  | _ -> [] 

let rec filter lst =
  match lst with
  | [] -> []
  | h :: t -> if h = [] then filter t else h :: filter t


let group lst =
  if valid lst then
    let grouped = grouper lst [] [] in
    let filtered = filter grouped in
    if filtered = [] then None else Some filtered
  else
    None
;