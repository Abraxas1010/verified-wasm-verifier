import Mathlib.LinearAlgebra.Prod
import HeytingLean.LoF.Combinators.Differential.Exponential

/-!
# Differential combinators: codereliction interface

This file packages the “codereliction” API expected by the aspirational DiLL plan.

We reuse the lightweight exponential model from `Exponential.lean`:

* `!V := Exp V := (ℕ →₀ V)`
* `codereliction : V →ₗ[K] !V`   (embed into degree 1)
* `dereliction  : !V →ₗ[K] V`   (project degree 1)

It also provides the basic additive “co-” operations (`coweakening`, `cocontraction`) and a
`sub`-style “codereliction gives derivatives” lemma (for additive groups).
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

namespace Exp

variable {K : Type*} [CommSemiring K]
variable {V : Type*} [AddCommMonoid V] [Module K V]

/-- Coweakening in the lightweight model: the zero element of `!V`. -/
def coweakening : Exp V :=
  0

/-- Cocontraction in the lightweight model: pointwise addition of graded components. -/
noncomputable def cocontraction : (Exp V × Exp V) →ₗ[K] Exp V :=
  LinearMap.fst K (Exp V) (Exp V) + LinearMap.snd K (Exp V) (Exp V)

end Exp

namespace Exp

variable {K : Type*} [CommRing K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Codereliction gives an “exact” increment law for linear maps, phrased as a difference. -/
theorem codereliction_is_derivative (f : Exp V →ₗ[K] W) (v dv : V) :
    f (codereliction (K := K) (V := V) (v + dv)) - f (codereliction (K := K) (V := V) v) =
      (f.comp (codereliction (K := K) (V := V))) dv := by
  refine (sub_eq_iff_eq_add).2 ?_
  simp [codereliction, add_comm]

end Exp

end Differential
end Combinators
end LoF
end HeytingLean
