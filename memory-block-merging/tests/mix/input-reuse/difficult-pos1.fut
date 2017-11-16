-- Similar to reuse/input-reuse/difficult-pos0.fut, but with two dimensions.
-- Requires coalescing for the input and output memory blocks to have the same
-- size.
-- ==
-- input { [[2, 5, 9], [1, 2, 3]] }
-- output { [[25, 175, 585], [5, 25, 60]] }
-- structure gpu { Alloc 0 }
-- structure cpu { Alloc 0 }

let difficult (x: i32): i32 =
  -- The loop has the last use of x.
  let y = loop y = 0 for i < x do
    y + x + i

  -- z is the return value and can reuse the memory associated with x.
  let z = y * 5
  in z

let main (xss: *[][]i32): [][]i32 =
  map (\xs -> map difficult xs) xss
