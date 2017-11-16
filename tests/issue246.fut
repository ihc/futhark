-- We assigned overly complex (and wrong) index functions to splits.
--
-- ==
-- input { 3 4 }
-- output { [1i32, 2i32, 5i32, 6i32, 9i32, 10i32] }

import "/futlib/math"

let dim_2 't [d0] [d1] (i: i32) (x: [d0][d1]t): i32 =
  if (i == 1)
  then d1
  else d0

let take_arrint (l: i32) (x: [][]i32): [][]i32 =
  if (0 <= l)
  then if (l <= length x)
  then let (v1, _) = split (l) (x) in
  v1
  else concat (x) (replicate ((i32.abs (l) - length x)) (replicate (dim_2 1 x) (0)))
  else if (0 <= (l + length x))
  then let (_, v2) = split ((l + length x)) (x) in
  v2
  else concat (replicate ((i32.abs (l) - length x)) (replicate (dim_2 1 x) (0))) (x)
let reshape_int (l: i32) (x: []i32): []i32 =
  let roundUp = ((l + (length x - 1)) / length x) in
  let extend = reshape (((length x * roundUp))) (replicate (roundUp) (x)) in
  let (v1, _) = split (l) (extend) in
  v1
entry main (n: i32, m: i32): []i32 =
  let t_v1 = reshape ((n,
                       m)) (reshape_int ((n * (m * 1))) (reshape (((length (map (\(x: i32): i32 ->
                                                                                (x + 1)) (iota (n*m)))) * 1)) (map (\(x: i32): i32 ->
                                                                                                                      (x + 1)) (iota (12))))) in
  let t_v2 = rearrange (1, 0) (t_v1) in
  let t_v3 = take_arrint (2) (t_v2) in
  let t_v4 = rearrange (1, 0) (t_v3) in
  reshape ((length t_v4 * ((dim_2 1 t_v4) * 1))) (t_v4)
