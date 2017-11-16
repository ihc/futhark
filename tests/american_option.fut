-- Port of Ken Friis Larsens pricer for American Put Options:
--
-- https://github.com/kfl/american-options.
--
-- This implementation is a straightforward sequential port - it is
-- fairly slow on the GPU.
--
-- ==
-- tags { no_python }
--          input { 1  } output { 6.745433 }
-- compiled input { 8  } output { 13.945689 }
-- compiled input { 16 } output { 16.222591 }
-- compiled input { 30 } output { 17.653706 }
-- compiled input { 64 } output { 18.429932 }

-- constants

import "/futlib/math"
import "/futlib/array"

let strike(): i32 = 100
let bankDays(): i32 = 252
let s0(): i32 = 100
let r(): f64 = 0.03
let alpha(): f64 = 0.07
let sigma(): f64 = 0.20

let binom(expiry: i32): f64 =
  let n = expiry * bankDays()
  let dt = r64(expiry) / r64(n)
  let u = f64.exp(alpha()*dt+sigma()*f64.sqrt(dt))
  let d = f64.exp(alpha()*dt-sigma()*f64.sqrt(dt))
  let stepR = f64.exp(r()*dt)
  let q = (stepR-d)/(u-d)
  let qUR = q/stepR
  let qDR = (1.0-q)/stepR

  let uPow = map (u**) (map r64 (iota(n+1)))
  let dPow = map (d**) (map r64 (map (n-) (iota(n+1))))
  let st = map (r64(s0())*) (map (*) uPow dPow)
  let finalPut = map (f64.max(0.0)) (map (r64(strike())-) st) in
  let put = loop put = finalPut for i in reverse (map (1+) (iota n)) do
    let (uPow_start, _) = split (i) uPow
    let (_, dPow_end) = split (n+1-i) dPow
    let st = map (r64(s0())*) (map (*) uPow_start dPow_end)
    let (_, put_tail) = split (1) put
    let (put_init, _) = split (length put-1) put in
    map (\(x,y) -> f64.max x y)
    (zip
     (map (r64(strike())-) st)
     (map (+)
      (map (qUR*) (put_tail))
      (map (qDR*) (put_init))))
  in put[0]

let main(expiry: i32): f64 =
  binom(expiry)
