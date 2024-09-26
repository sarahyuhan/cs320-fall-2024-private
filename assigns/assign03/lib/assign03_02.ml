let rec nth lst n =
  match lst, n with
  | [], _ -> failwith "out of bounds"
  | h::_, 0 -> h
  | _::t, n -> nth t (n-1)

let rec take lst n =
  match lst, n with
  | [], _ -> []
  | _, 0 -> []
  | x :: xs, n -> x :: take xs (n - 1)

let rec sum lst =
  match lst with
  |[]-> 0
  |h::t -> h + sum t

let rec reverse lst =
  match lst with
  | [] -> []
  | h :: t -> (reverse t) @ [h]

let gen_fib (l : int list) (k : int) : int =
  let len = 
    let rec length lst acc =
      match lst with
      |[]-> acc
      |_::t -> length t (acc+1)
    in length l 0
  in
 
  let rec calc list current =
    if current < len then
      nth l current
    else
      let previous = reverse (take list len) in
      let next = sum previous in
      calc (next :: list) (current - 1)
  in
  calc (reverse l) k
;;