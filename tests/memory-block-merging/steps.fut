-- Memory block merging with a couple of steps.

fun main (ms: []i32, n: i32): []i32 =
  let t0 = map (+ 1) ms
  let t1 = map (/ t0[n - 2]) (iota n)
  in t1
