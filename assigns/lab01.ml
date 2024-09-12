let rec modulo n k =
  if n <= k then n
  else modulo (n-k) k

let rec sqrt n =
  