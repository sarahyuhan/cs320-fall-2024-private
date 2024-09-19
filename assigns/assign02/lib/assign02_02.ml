type matrix = {
  entries : float list list;
  rows : int;
  cols : int;
}

let rec split c lst =
  match c, lst with
  | 0, _ -> ([], lst)
  | _, [] -> ([], [])
  | _, x :: xs -> 
      let first, rest = split (c - 1) xs in
      (x :: first, rest)

let rec slice lst c =
  match lst with
  | [] -> []
  | _ -> let row, t = split c lst in
    row :: slice t c

let mk_matrix (entries : float list) ((r, c) : int * int) : matrix =
  let sliced = slice entries c in
  { entries = sliced; rows = r; cols = c }
;;


let _ =
  let a = mk_matrix [1.;0.;0.;1.] (2, 2) in
  let b = {entries = [[1.;0.];[0.;1.]]; rows = 2; cols = 2} in
  assert (a = b)