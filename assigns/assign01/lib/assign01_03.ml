let is_prime n =
  let rec go i =
    if i * i > n then
      true
    else if n mod i = 0 then
      false
    else
      go (i + 1)
  in
  if n < 2 then false
  else go 2
;;

let nth_prime n =
  let rec nth_find times number =
    if times = n && is_prime number then number
    else if is_prime number then nth_find (times+1) (number+1)
    else nth_find times (number+1)
  in
  nth_find 0 2
;;

let nth s i =
  let prime = nth_prime i in
  let rec exp s prime times =
    if s mod prime = 0 then exp (s/prime) prime (times+1)
    else times
  in exp s prime 0 ;;