let rec pow n k = 
  if k = 0 then 1
  else n * pow n (k-1);;