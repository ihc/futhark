-- ==
-- structure { Map 2 }
let main (a_1: [][]i32, a_2: [][]i32): [][]i32 =
  let a = map (\(a_1r: []i32) (a_2r: []i32)  -> zip a_1r a_2r) (
                  a_1) (a_2)
  let b = map (\(row: [](i32,i32))  ->
                map (\(x: i32, y: i32): (i32,i32)  ->
                      (x+y,x-y)) row) a
  let c = map (\(row: [](i32,i32))  ->
                map (\(x,y) -> x + y) row)
              (rearrange (1,0) b)
  in c
