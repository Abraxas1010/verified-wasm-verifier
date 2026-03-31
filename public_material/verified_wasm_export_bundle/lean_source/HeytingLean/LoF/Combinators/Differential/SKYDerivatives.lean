import HeytingLean.LoF.Combinators.Differential.Derivative

/-!
# Differential combinators: explicit SKY derivatives

This file packages “named” derivative facts for the primitive SKY combinators in the Differential
slice, and provides a witness-based interface for the Y-derivative fixed-point equation.

Notes:
* K and S derivatives are already provided in `Derivative.lean` (as `K_jacobian` and `S_derivative`).
* Y is treated *partially*: we do not claim a global derivative exists; instead we expose a linear
  fixed-point equation and an existence predicate under an “invertibility” hypothesis.
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

section KS

variable {K : Type*} [CommSemiring K]

theorem K_jacobian_fst : (K_jacobian (K := K)).1 = LinearMap.id := rfl
theorem K_jacobian_snd : (K_jacobian (K := K)).2 = 0 := rfl

end KS

/-! ## Y derivative witnesses -/

section Y

variable {K : Type*} [CommRing K]

def Y_apply (f : FormalSum K) : FormalSum K :=
  (single (K := K) LoF.Comb.Y) ⬝ f

/-- A witness that `d` solves the (linear) Y-derivative equation:

`d = df (Y f) + f d`.

We phrase the recursive term using the linear map `derivativeApp2 f` (left application). -/
structure YDerivativeWitness (f df : FormalSum K) where
  derivative : FormalSum K
  satisfies :
    derivative =
      (df ⬝ Y_apply (K := K) f) + (derivativeApp2 (K := K) f) derivative

/-- A sufficient condition for the Y-derivative to exist: `(id - (v ↦ f v))` has a right inverse. -/
def Y_derivative_exists (f : FormalSum K) : Prop :=
  ∃ inv : FormalSum K →ₗ[K] FormalSum K,
    (((LinearMap.id : FormalSum K →ₗ[K] FormalSum K) - derivativeApp2 (K := K) f).comp inv = LinearMap.id)

/-- Construct a Y-derivative witness from a right inverse of `(id - (v ↦ f v))`. -/
def yDerivativeWitness_of_rightInverse
    (f df : FormalSum K)
    (inv : FormalSum K →ₗ[K] FormalSum K)
    (hinv :
      (((LinearMap.id : FormalSum K →ₗ[K] FormalSum K) - derivativeApp2 (K := K) f).comp inv = LinearMap.id)) :
    YDerivativeWitness (K := K) f df := by
  classical
  let rhs : FormalSum K := df ⬝ Y_apply (K := K) f
  refine
    { derivative := inv rhs
      satisfies := ?_ }
  have hsol :
      ((LinearMap.id : FormalSum K →ₗ[K] FormalSum K) - derivativeApp2 (K := K) f) (inv rhs) = rhs := by
    have := congrArg (fun L => L rhs) hinv
    simpa [LinearMap.comp_apply] using this
  have hsol' : inv rhs - (derivativeApp2 (K := K) f) (inv rhs) = rhs := by
    simpa using hsol
  have hEq : inv rhs = rhs + (derivativeApp2 (K := K) f) (inv rhs) :=
    (sub_eq_iff_eq_add).1 hsol'
  simpa [rhs] using hEq

/-- A trivial witness: when `df = 0`, the zero tangent solves the linear Y-derivative equation. -/
def yDerivativeWitness_zero (f : FormalSum K) :
    YDerivativeWitness (K := K) f (0 : FormalSum K) := by
  refine { derivative := 0, satisfies := ?_ }
  simp [Y_apply, derivativeApp2_apply, FormalSum.app_zero_left, FormalSum.app_zero_right]

/-- Existence lemma: there is always a Y-derivative witness for `df = 0`, with derivative `0`. -/
theorem Y_derivative_constant (f : FormalSum K) :
    ∃ w : YDerivativeWitness (K := K) f (0 : FormalSum K), w.derivative = 0 := by
  exact ⟨yDerivativeWitness_zero (K := K) f, rfl⟩

/-- Fuel-bounded approximation to the Y-derivative fixed-point equation `d = df (Y f) + f d`. -/
def yDerivativeApprox (fuel : Nat) (f df : FormalSum K) : FormalSum K :=
  let base : FormalSum K := df ⬝ Y_apply (K := K) f
  Nat.rec (motive := fun _ => FormalSum K) 0 (fun _ d => base + (derivativeApp2 (K := K) f) d) fuel

end Y

end Differential
end Combinators
end LoF
end HeytingLean
