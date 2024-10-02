let rec reverse lst =
  match lst with
  | [] -> []
  | h :: t -> (reverse t) @ [h]


let valid lst =
  let rec check lst previous =
    match lst with
    | [] -> true
    | [x] -> x <> 0 (* Single element cannot be zero *)
    | x1 :: x2 :: rest ->
        if x1 = 0 then false  (* Zero cannot be at the start *)
        else if x2 = 0 then
          if previous * x1 > 0 then false  (* Check for opposite signs around zero *)
          else check rest 0
        else if x1 * x2 < 0 then false  (* Adjacent elements must have the same sign *)
        else check (x2 :: rest) x1
  in
  match lst with
  | [] -> true  (* Empty list is valid *)
  | x :: xs -> check xs x

let rec grouper lst current acc =
  match lst with
  | [] -> reverse (reverse current :: acc)  (* Final reverse to group accumulated lists *)
  | 0 :: rest -> grouper rest [] (reverse current :: acc)  (* Zero splits the group *)
  | x :: rest ->
      (match current with
      | [] -> grouper rest [x] acc  (* If current is empty, start a new group with x *)
      | y::_ when (x * y) > 0 -> grouper rest (x :: current) acc  (* Same sign, add to current *)
      | _ -> [])

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
  ;;