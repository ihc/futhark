-- Memory block merging with array assignment.

fun main (nss: [][]i32, ms: []i32): [][]i32 =
  let t0 = copy nss
  let t0[0] = map (+ 1) ms
  in t0
