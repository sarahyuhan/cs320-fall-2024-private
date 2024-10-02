type tree = 
| Leaf of int
| Node of tree list

let rec flat lst =
  match lst with
  | [] -> []
  | Leaf h :: t -> Leaf h :: flat t
  | Node children :: t -> flat children @ flat t
;;


let rec map f lst =
  match lst with
  | [] -> []
  | x :: xs -> (f x) :: map f xs

let rec height t =
  match t with
  | Leaf _ -> 0
  | Node children ->
      let heights = map height children in
      1 + List.fold_left max 0 heights

let rec short lst =
  match lst with
  | [] -> []
  | h :: t -> h @ short t

let rec element t =
  match t with
  | Leaf x -> [Leaf x]
  | Node children -> short (map element children)

let rec collapse h t =
  if h <= 0 then t
  else
    match t with
    | Leaf _ -> t
    | Node children ->
        if height t <= h then t
        else
          let collapsed_children = map (collapse (h - 1)) children in
          let terminals = short (map element collapsed_children) in
          Node terminals
;;
