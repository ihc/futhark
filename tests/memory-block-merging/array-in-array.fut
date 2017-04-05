-- Memory block merging with array assignment.

fun main (nss: [][]i32, ms: []i32): [][]i32 =
  let y = copy nss
  let b = map (+ 1) ms
  let y[0] = b
  in y
