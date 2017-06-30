let add (a : i32) (b : i32) : i32 =
  a + b

let subtract (a : i32) (b : i32) : i32 =
  a - b

let main() =
  let c = 30
  let d = 40 in
  if c > d
  then add c d
  else subtract c d
