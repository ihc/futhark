-- && must be short-circuiting.
--
-- ==
-- input { 0 [true, true] } output { true }
-- input { 1 [true, true] } output { true }
-- input { 2 [true, true] } output { false }

let main [n] (i: i32, bs: [n]bool): bool =
  i < n && bs[i]
