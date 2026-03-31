import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Group

import HeytingLean.Moonshine.Modular.Delta
import HeytingLean.Moonshine.Modular.QParam

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane Function Complex

local notation "𝕢" => Periodic.qParam

/-- The cusp-side expression for `Δ`, as a function of `q` (power kept outside the infinite product). -/
noncomputable def Delta_cusp (q : ℂ) : ℂ :=
  q * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ (24 : Nat)

private lemma one_sub_pow_ne_zero_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    (1 : ℂ) - q ^ (n + 1) ≠ 0 := by
  -- If `q^(n+1) = 1`, then taking norms gives `‖q‖^(n+1) = 1`, contradicting `‖q‖ < 1`.
  refine sub_ne_zero.mpr ?_
  intro hEq
  have hnorm' : (1 : ℝ) = ‖q‖ ^ (n + 1) := by
    -- `‖q^(n+1)‖ = ‖q‖^(n+1)` and `‖(1 : ℂ)‖ = 1`.
    have := congrArg norm hEq
    simpa [norm_pow] using this
  have hnorm : ‖q‖ ^ (n + 1) = (1 : ℝ) := hnorm'.symm
  have hlt : ‖q‖ ^ (n + 1) < (1 : ℝ) :=
    pow_lt_one₀ (norm_nonneg q) hq (n := n + 1) (by exact Nat.succ_ne_zero n)
  exact (ne_of_lt hlt) hnorm

private lemma qParam_24_pow_24 (z : ℂ) : (𝕢 24 z) ^ (24 : Nat) = 𝕢 1 z := by
  -- Unfold `qParam` and use `exp_nat_mul`.
  simp [Periodic.qParam, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
    ← Complex.exp_nat_mul]

lemma Delta_eq_Delta_cusp (τ : ℍ) : Delta τ = Delta_cusp (q τ) := by
  -- Expand `Delta` and `eta`, then simplify to the `q`-side expression.
  have : (ModularForm.eta (τ : ℂ)) ^ (24 : Nat) =
      (𝕢 1 (τ : ℂ)) * (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ)) ^ (n + 1))) ^ (24 : Nat) := by
    -- `eta = qParam 24 * tprod (...)`.
    simp [ModularForm.eta, ModularForm.eta_q, mul_pow, qParam_24_pow_24]
  -- Repackage as `Delta_cusp (q τ)`.
  simpa [Delta, eta, q, Delta_cusp] using this

/-!
`Delta_cusp` is primarily used as a rewriting target for `Delta (τ : ℍ)` into the `q`-coordinate.
For nonvanishing statements, prefer pulling back to `ℍ` and using `Delta_ne_zero`.
-/

lemma Delta_cusp_ne_zero_of_norm_lt_one_of_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    Delta_cusp q ≠ 0 := by
  -- The infinite product is nonzero since `∑ ‖q^(n+1)‖` converges for `‖q‖ < 1`.
  have hs : Summable (fun n : ℕ => ‖-(q ^ (n + 1))‖) := by
    -- Reduce to a geometric series in `‖q‖`.
    have hs' : Summable (fun n : ℕ => ‖q‖ ^ (n + 1)) := by
      have hgeom : Summable (fun n : ℕ => (‖q‖ : ℝ) ^ n) :=
        summable_geometric_of_lt_one (norm_nonneg q) hq
      -- Multiply by `‖q‖` to shift the exponent by `+1`.
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using (hgeom.mul_left ‖q‖)
    simpa [norm_neg, norm_pow] using hs'
  have hprod : (∏' n : ℕ, (1 - q ^ (n + 1))) ≠ 0 := by
    -- Apply the standard nonvanishing criterion for absolutely convergent products.
    refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(q ^ (n + 1))) ?_ hs
    intro n
    simpa [sub_eq_add_neg] using one_sub_pow_ne_zero_of_norm_lt_one (q := q) hq n
  -- Now `Delta_cusp q = q * (product)^24`.
  simp [Delta_cusp, hq0, hprod]

lemma Delta_cusp_ne_zero_of_eq_q (τ : ℍ) : Delta_cusp (q τ) ≠ 0 := by
  intro h0
  have hΔ : Delta τ = 0 := by
    -- Rewrite `Delta τ` via the cusp bridge.
    simpa [Delta_eq_Delta_cusp (τ := τ)] using h0
  exact (Delta_ne_zero τ) hΔ

end HeytingLean.Moonshine.Modular
