-- Memory block merging with where it can only be performed on a sub-body.

let main (n: i32, i: i32, cond: bool): [n][n]i32 =
  let nss = replicate n (iota n)
  let result =
    if cond
    then let ms = map (+ 10) (iota n)
         let nss[i] = ms -- This should be coalesced.
         in nss
    else nss
  in result
