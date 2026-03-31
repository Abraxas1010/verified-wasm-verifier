/-!
# DFT (Float-based) — general-N, no mathlib trig

This module provides a simple Float-based DFT/IDFT using polynomial
approximations for sin/cos. It is intended for demos and small sizes,
and avoids heavy mathlib imports on the CLI path. The implementation
operates over arrays for convenience.
-/

namespace HeytingLean
namespace Analysis
namespace DFTFloat

private def twoPi : Float := 6.2831853071795864769
private def halfPi : Float := 1.5707963267948966192

private def mod2pi (θ : Float) : Float :=
  let k := (θ / twoPi).floor
  let kInt : Int := Int64.toInt (Float.toInt64 k)
  θ - twoPi * (Float.ofInt kInt)

-- Reduce angle to [-π, π] then to [-π/2, π/2] using symmetries
private def reduce (θ : Float) : (Float × Int × Int) :=
  let t := mod2pi θ
  let pi : Float := 3.1415926535897932384
  let t' := if t > pi then t - twoPi else t
  let s := if t' > halfPi then (pi - t', 1, 0)
           else if t' < -halfPi then (-(pi + t'), 1, 0)
           else (t', 0, 0)
  s

-- 7th-order Taylor approximations around 0 (for small |x|)
private def sinSeries (x : Float) : Float :=
  let x2 := x*x
  let x3 := x2*x
  let x5 := x3*x2
  let x7 := x5*x2
  x - (x3 / 6.0) + (x5 / 120.0) - (x7 / 5040.0)

private def cosSeries (x : Float) : Float :=
  let x2 := x*x
  let x4 := x2*x2
  let x6 := x4*x2
  1.0 - (x2 / 2.0) + (x4 / 24.0) - (x6 / 720.0)

private def sinApprox (θ : Float) : Float :=
  let (x, flip, _) := reduce θ
  let s := sinSeries x
  if flip = 1 then s else s

private def cosApprox (θ : Float) : Float :=
  let (x, flip, _) := reduce θ
  let c := cosSeries x
  if flip = 1 then -c else c

/-- DFT over real input: returns array of (re, im). -/
def dft (xs : Array Float) : Array (Float × Float) := Id.run do
  let n := xs.size
  let mut out : Array (Float × Float) := #[]
  for k in [0:n] do
    let mut re : Float := 0.0
    let mut im : Float := 0.0
    for nn in [0:n] do
      let θ := -twoPi * (Float.ofNat k) * (Float.ofNat nn) / (Float.ofNat n)
      let c := cosApprox θ
      let s := sinApprox θ
      let x := xs[nn]!
      re := re + x * c
      im := im + x * s
    out := out.push (re, im)
  return out

/-- IDFT back to real (reconstruction by averaging the conjugate kernel). -/
def idft (spec : Array (Float × Float)) : Array Float := Id.run do
  let n := spec.size
  let mut out : Array Float := #[]
  for nn in [0:n] do
    let mut r : Float := 0.0
    for k in [0:n] do
      let θ := twoPi * (Float.ofNat k) * (Float.ofNat nn) / (Float.ofNat n)
      let c := cosApprox θ
      let s := sinApprox θ
      let (re, im) := spec[k]!
      r := r + (re * c - im * s)
    r := r / (Float.ofNat n)
    out := out.push r
  return out

end DFTFloat
end Analysis
end HeytingLean
