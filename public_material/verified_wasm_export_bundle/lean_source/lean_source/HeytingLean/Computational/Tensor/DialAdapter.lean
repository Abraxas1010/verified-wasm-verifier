import HeytingLean.Computational.Tensor.Core
import HeytingLean.Computational.Tensor.Nucleus

/-
Dial → Temperature adapters for the Tensor scaffold.
We keep this numeric and lightweight (Floats + Arrays only).
-/

namespace HeytingLean
namespace Computational
namespace Tensor

structure TempRange where
  minT : Float := 0.0
  maxT : Float := 1.0

@[simp] def TempRange.clamp (r : TempRange) (t : Float) : Float :=
  if t < r.minT then r.minT else if t > r.maxT then r.maxT else t

@[simp] def linearMap (r : TempRange) (level maxLevel : Nat) : Float :=
  let denom := if maxLevel = 0 then 1 else maxLevel
  let frac  := (Float.ofNat level) / (Float.ofNat denom)
  r.clamp (r.minT + (r.maxT - r.minT) * frac)

@[simp] def easeExp (gamma : Float) (x : Float) : Float :=
  -- simple exponential easing for [0,1]; no safety for negatives
  if x ≤ 0.0 then 0.0 else if x ≥ 1.0 then 1.0 else x ^ gamma

@[simp] def easedMap (r : TempRange) (gamma : Float)
    (level maxLevel : Nat) : Float :=
  let denom := if maxLevel = 0 then 1 else maxLevel
  let x := (Float.ofNat level) / (Float.ofNat denom)
  let y := easeExp gamma x
  r.clamp (r.minT + (r.maxT - r.minT) * y)

@[simp] def withTemp {α} (N : TensorNucleus α) (t : Float) : TensorNucleus α :=
  { N with temperature := t }

@[simp] def withDialLevel {α}
    (N : TensorNucleus α) (r : TempRange)
    (level maxLevel : Nat) : TensorNucleus α :=
  withTemp N (linearMap r level maxLevel)

@[simp] def withDialLevelEased {α}
    (N : TensorNucleus α) (r : TempRange) (gamma : Float)
    (level maxLevel : Nat) : TensorNucleus α :=
  withTemp N (easedMap r gamma level maxLevel)

end Tensor
end Computational
end HeytingLean

