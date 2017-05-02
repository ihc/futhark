-- Potentially negative test.  Depends on how we treat memory block merging that
-- results in slow array access through a correct but bad index function
-- translation using IxFun's Permute.
-- ==
-- input { [[0, 1],
--          [2, 3]]
--         [10, 15]
--         0
--       }
-- output { [[20, 25],
--           [1, 3]]
--        }

import "/futlib/array"

let main (xs0: *[#n][#n]i32, ys0: [#n]i32, i: i32): [n][n]i32 =
  let xs = transpose xs0
  let ys = map (+ 10) ys0
  let xs[i] = ys
  in xs
