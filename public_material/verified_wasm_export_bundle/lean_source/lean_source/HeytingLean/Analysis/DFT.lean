import HeytingLean.Analysis.FourierCore
-- No extra array imports needed for core operations

namespace HeytingLean
namespace Analysis

open scoped BigOperators

/-!
# Complex DFT on `Fin N` and arrays

This module provides a small, mathlib-backed DFT/IDFT over complex-valued
signals on `Fin N`, along with array conveniences. Proof obligations are
kept light (no proof holes), suitable for strict builds.
-/

/-! ## Function ↔ Array bridges -/

@[simp] def ofArrayFun {N : ℕ} (f : Fin N → ℂ) : Array ℂ := Array.ofFn f

@[simp] def toArrayFun (xs : Array ℂ) : Fin xs.size → ℂ := fun n => xs[n]

/-- DFT over arrays: coerces to `Fin N → ℂ` with `N = xs.size`. -/
noncomputable def dftArray (xs : Array ℂ) : Array ℂ :=
  let N := xs.size
  ofArrayFun (N := N) (dft (N := N) (toArrayFun xs))

/-- IDFT over arrays: coerces to `Fin N → ℂ` with `N = spec.size`. -/
noncomputable def idftArray (spec : Array ℂ) : Array ℂ :=
  let N := spec.size
  ofArrayFun (N := N) (idft (N := N) (toArrayFun spec))

/-! ## Discrete circular convolution and helpers (arrays)

These array utilities avoid heavy dependencies and are intended for demos/tests.
-/

def circConvArray (xs ys : Array ℂ) : Array ℂ := Id.run do
  let n := xs.size
  if ys.size ≠ n then
    -- size mismatch → return empty array (conservative guard)
    return #[]
  let mut out : Array ℂ := Array.replicate n (0 : ℂ)
  for k in [0:n] do
    let mut acc : ℂ := 0
    for j in [0:n] do
      let idx := (k + n - j) % n
      acc := acc + xs[j]! * ys[idx]!
    out := out.set! k acc
  return out

def pointwiseMul (as bs : Array ℂ) : Array ℂ := Id.run do
  let n := min as.size bs.size
  let mut out : Array ℂ := #[]
  for i in [0:n] do
    out := out.push (as[i]! * bs[i]!)
  return out

end Analysis
end HeytingLean
