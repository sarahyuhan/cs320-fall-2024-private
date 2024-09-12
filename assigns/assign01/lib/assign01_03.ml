open Assign01_02

let nth s i =
  let prime = nth_prime i in
  let rec exp s prime times =
    if s mod prime = 0 then exp (s/prime) prime (times+1)
    else times
  in exp s prime 0 ;;
