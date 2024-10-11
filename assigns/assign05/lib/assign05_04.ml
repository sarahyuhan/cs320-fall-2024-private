type set_info = {
  ind : int -> bool;
  mn : int;
  mx : int;
}

module ListSet = struct
  type t = int list

  let empty = []

  let singleton x = [x]

  let rec mem x = function
    | [] -> false
    | h::t ->
      if x = h then true
      else if x < h then false
      else mem x t

  let card x = List.length x

  let rec union list1 list2 =
    match list1, list2 with
    | [], x | x, [] -> x
    | h::t, h2::t2 ->
      if h = h2 then h::union t t2
      else if h < h2 then h::union t list2
      else h2::union list1 t2
  end

  module FuncSet = struct
    type t = set_info

    let empty = {
      ind = (fun _ -> false);
      mn = min_int;
      mx = max_int;
    }

    let singleton x = {
      ind = (fun y -> y = x);
      mn = x;
      mx = x;
    }

    let mem x set = set.ind x

    let card set =
      let rec count acc x =
        if x > set.mn then acc
        else if set.ind x then count (acc+1) (x+1)
        else count acc (x+1)
      in
      if set.mn > set.mn then 0 else count 0 set.mx

    let union set set2 =
      let newInd x = set.ind x || set2.ind x in
      let newMN = min set.mn set2.mn in
      let newMX = max set.mx set2.mx in
      {ind = newInd; mn = newMN; mx = newMX}
    end