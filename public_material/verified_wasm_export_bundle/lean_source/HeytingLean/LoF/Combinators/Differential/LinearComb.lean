import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Finsupp.LSum
import HeytingLean.LoF.Combinators.SKYMultiway
import HeytingLean.LoF.Combinators.Differential.VectorSpace

/-!
# Differential combinators: linear extension of application and stepping

This file provides:
- `app`      : bilinear extension of `Comb.app` to formal sums.
- `appBilin` : the same operation bundled as a bilinear `LinearMap`.
- `stepSum`  : formal superposition of one-step successors, via `Comb.stepEdgesList`.
- `steps`    : linear extension of `stepSum` to formal sums.
- bounded iterates / reachability operators (useful as a runtime approximation).
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

namespace FormalSum

variable {K : Type*} [Semiring K]

/-- Bilinear extension of syntactic application: distribute over formal sums. -/
def app (v w : FormalSum K) : FormalSum K :=
  v.sum (fun t a => w.sum (fun u b => Finsupp.single (LoF.Comb.app t u) (a * b)))

infixl:70 " ⬝ " => app

@[simp]
theorem app_single_single (t u : LoF.Comb) :
    (single (K := K) t) ⬝ (single (K := K) u) = single (K := K) (LoF.Comb.app t u) := by
  classical
  simp [app, single, Finsupp.sum_single_index]

end FormalSum

namespace FormalSum

variable {K : Type*} [CommSemiring K]

noncomputable def appRight (t : LoF.Comb) : FormalSum K →ₗ[K] FormalSum K :=
  Finsupp.lsum K (fun u => (Finsupp.lsingle (LoF.Comb.app t u) : K →ₗ[K] FormalSum K))

noncomputable def appBilin : FormalSum K →ₗ[K] FormalSum K →ₗ[K] FormalSum K :=
  Finsupp.lsum K (fun t =>
    ((LinearMap.lsmul K (FormalSum K →ₗ[K] FormalSum K)).flip (appRight (K := K) t)))

@[simp]
theorem appRight_apply (t : LoF.Comb) (w : FormalSum K) :
    appRight (K := K) t w = FormalSum.app (K := K) (single (K := K) t) w := by
  classical
  -- Unfold the linear extension and the bilinear definition of `app` on a singleton.
  -- `lsingle` is the bundled version of `Finsupp.single`.
  simp [appRight, FormalSum.app, single, Finsupp.lsum_apply]
  change (Finsupp.sum w fun i b => (Finsupp.lsingle (t.app i) : K →ₗ[K] FormalSum K) b) =
      Finsupp.sum w fun u b => Finsupp.single (t.app u) b
  simp [Finsupp.lsingle_apply]

@[simp]
theorem appBilin_apply_apply (v w : FormalSum K) :
    (appBilin (K := K) v) w = FormalSum.app (K := K) v w := by
  classical
  -- `appBilin` is the linear extension in `v` of `t ↦ appRight t`, matching the `sum` definition of `app`.
  -- Reduce to the coefficient-wise sums and use that scalar multiplication on `FormalSum` scales coefficients.
  simp [appBilin, FormalSum.app, appRight, Finsupp.lsum_apply]
  -- Convert the `lsingle`-based inner sum to an explicit `Finsupp.single` sum.
  change
    (Finsupp.sum v fun i d =>
        d • Finsupp.sum w fun u b => (Finsupp.lsingle (i.app u) : K →ₗ[K] FormalSum K) b) =
      Finsupp.sum v fun t a => Finsupp.sum w fun u b => Finsupp.single (t.app u) (a * b)
  simp [Finsupp.lsingle_apply]
  -- Push the scalar `d` into the inner `w.sum` and into the `single` coefficient.
  simp [Finsupp.sum, Finset.smul_sum]

/-! ## Bilinearity lemmas for `FormalSum.app`

These are convenience lemmas for rewriting expressions produced by `dualApp`/`S_derivative`.
They are proved by transporting the corresponding linearity facts from `appBilin`.
-/

theorem app_add_left (v₁ v₂ w : FormalSum K) :
    FormalSum.app (K := K) (v₁ + v₂) w =
      FormalSum.app (K := K) v₁ w + FormalSum.app (K := K) v₂ w := by
  calc
    FormalSum.app (K := K) (v₁ + v₂) w = (appBilin (K := K) (v₁ + v₂)) w :=
      (appBilin_apply_apply (K := K) (v₁ + v₂) w).symm
    _ = ((appBilin (K := K) v₁) w) + ((appBilin (K := K) v₂) w) := by
      simp [LinearMap.map_add, LinearMap.add_apply]
    _ = FormalSum.app (K := K) v₁ w + FormalSum.app (K := K) v₂ w := by
      simp [appBilin_apply_apply (K := K)]

theorem app_add_right (v w₁ w₂ : FormalSum K) :
    FormalSum.app (K := K) v (w₁ + w₂) =
      FormalSum.app (K := K) v w₁ + FormalSum.app (K := K) v w₂ := by
  calc
    FormalSum.app (K := K) v (w₁ + w₂) = (appBilin (K := K) v) (w₁ + w₂) :=
      (appBilin_apply_apply (K := K) v (w₁ + w₂)).symm
    _ = (appBilin (K := K) v) w₁ + (appBilin (K := K) v) w₂ := by
      exact LinearMap.map_add (appBilin (K := K) v) w₁ w₂
    _ = FormalSum.app (K := K) v w₁ + FormalSum.app (K := K) v w₂ := by
      simp [appBilin_apply_apply (K := K)]

theorem app_zero_left (w : FormalSum K) :
    FormalSum.app (K := K) (0 : FormalSum K) w = 0 := by
  calc
    FormalSum.app (K := K) (0 : FormalSum K) w = (appBilin (K := K) (0 : FormalSum K)) w :=
      (appBilin_apply_apply (K := K) (0 : FormalSum K) w).symm
    _ = 0 := by simp

theorem app_zero_right (v : FormalSum K) :
    FormalSum.app (K := K) v (0 : FormalSum K) = 0 := by
  calc
    FormalSum.app (K := K) v (0 : FormalSum K) = (appBilin (K := K) v) (0 : FormalSum K) :=
      (appBilin_apply_apply (K := K) v (0 : FormalSum K)).symm
    _ = 0 := by
      exact LinearMap.map_zero (appBilin (K := K) v)

end FormalSum

namespace FormalSum

variable {K : Type*} [Semiring K]

/-- Formal sum of one-step successors of a term, with coefficient `1` for each enumerated edge. -/
def stepSum (t : LoF.Comb) : FormalSum K :=
  (LoF.Comb.stepEdgesList t).foldl (fun acc e => acc + Finsupp.single e.2 1) 0

/-- Linear extension of one-step reduction to formal sums. -/
def steps (v : FormalSum K) : FormalSum K :=
  v.sum (fun t a => a • stepSum (K := K) t)

def stepsIter : Nat → FormalSum K → FormalSum K
  | 0, v => v
  | Nat.succ n, v => steps (K := K) (stepsIter n v)

def reachabilityBounded (fuel : Nat) (v : FormalSum K) : FormalSum K :=
  (Finset.range (fuel + 1)).sum (fun n => stepsIter (K := K) n v)

end FormalSum

end Differential
end Combinators
end LoF
end HeytingLean
