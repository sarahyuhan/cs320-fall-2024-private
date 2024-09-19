type dir = 
  | North
  | South
  | East
  | West

type path = dir list

let dist (dirs: path) : float =
  let rec coordinates (dirs: path) (x, y) =
    match dirs with
    | [] -> (x,y)
    | North::tl -> coordinates tl (x,y+1)
    | South::tl -> coordinates tl (x,y-1)
    | East::tl -> coordinates tl (x+1,y)
    | West::tl -> coordinates tl (x-1,y)
  in
  let (x, y) = coordinates dirs (0,0) in
  sqrt (float_of_int ((x*x) + (y*y)))
;;