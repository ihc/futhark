-- Memory block merging with a copy.  Requires allocation hoisting of the memory
-- block for 't1'.

let main (ns: []i32): []i32 =
  let t0 = map (+ 1) ns
  let t1 = copy t0
  in t1
