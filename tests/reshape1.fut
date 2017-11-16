-- ==
-- input {
--   [1,2,3,4,5,6,7,8,9]
-- }
-- output {
--   [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
-- }

import "/futlib/math"

let intsqrt(x: i32): i32 =
    t32(f32.sqrt(r32(x)))

let main [n] (a: [n]i32): [][]i32 =
    reshape (intsqrt(n), intsqrt(n)) a
