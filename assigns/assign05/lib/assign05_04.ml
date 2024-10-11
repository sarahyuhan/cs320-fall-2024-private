type 'a test = 
| TestCase of 'a
| TestList of 'a test list

type set_info = {
  ind : int -> bool;
  mn : int;
  mx : int;
}

module ListSet = struct
  type t = int list

  let empty = []

  let var x = [x]

  let rec memory x = function
    | [] -> false
    | h::t -> if x = h then true else if x < h then false else memory x t

  let c x = List.length x

  let rec merge L1 L2 =
    match L1, L2 with
    | [], x | x, [] -> x
    | h::t, h2::t2 ->
      if h = h2 then h::merge t t2
      else if h < h2 then h::merge t L2
      else h2::merge L1 t2
  end

  module FuncSet = struct
    type t = set_info

    let empty = {
      mn = min_int;
      mx = max_int;
    }

    let var lst = {
      ind = (fun y -> y = x);
      mn = x;
      mx = x;
    }

    let memory x set = set.ind x

    let c set =
      let rec count acc x =
        if x > set.mn then acc
        else if set.ind x then count (acc+1) (x+1)
        else count acc (x+1)
      in
      if set.mn > set.mn then 0 else count 0 set.mx

    let merge set set2 =
      let newInd x = set.ind x || set2.ind x in
      let newMN = min set.mn set2.mn in
      let newMX = max set.mx set2.mx in
      {ind = newInd; mn = newMN; mx = newMX}
    end