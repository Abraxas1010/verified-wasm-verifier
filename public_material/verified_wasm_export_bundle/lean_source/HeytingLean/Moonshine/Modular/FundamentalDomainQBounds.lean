import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt

import HeytingLean.Moonshine.Modular.QParam

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane
open scoped Modular

/-!
## Bounds on `q` in the Standard Fundamental Domain

These are small helper lemmas for "Gate A4" style estimates restricted to `ModularGroup.fd`.
-/

lemma one_half_le_im_of_mem_fd {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) : (1 / 2 : ℝ) ≤ τ.im := by
  have h3 : (3 : ℝ) ≤ 4 * τ.im ^ 2 :=
    ModularGroup.three_le_four_mul_im_sq_of_mem_fd (τ := τ) hτ
  have hquarter : (1 / 4 : ℝ) ≤ τ.im ^ 2 := by
    nlinarith [h3]
  have himpos : 0 < τ.im := τ.im_pos
  nlinarith [hquarter, himpos]

lemma norm_q_le_exp_neg_pi_of_mem_fd {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) :
    ‖q τ‖ ≤ Real.exp (-Real.pi) := by
  -- Use mathlib's general bound `‖qParam 1 ξ‖ ≤ exp(-π)` when `im ξ ≥ 1/2`.
  have him : (1 / 2 : ℝ) ≤ (τ : ℂ).im := by
    simpa using (one_half_le_im_of_mem_fd (τ := τ) hτ)
  have h :=
    Function.Periodic.norm_qParam_le_of_one_half_le_im (ξ := (τ : ℂ)) him
  simpa [q, HeytingLean.Moonshine.Modular.q] using h

lemma sqrt_three_div_two_le_im_of_mem_fd {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) :
    Real.sqrt 3 / 2 ≤ τ.im := by
  have h3 : (3 : ℝ) ≤ 4 * τ.im ^ 2 :=
    ModularGroup.three_le_four_mul_im_sq_of_mem_fd (τ := τ) hτ
  have h34 : (3 / 4 : ℝ) ≤ τ.im ^ 2 := by
    nlinarith [h3]
  have hsqrt : Real.sqrt (3 / 4 : ℝ) ≤ Real.sqrt (τ.im ^ 2) :=
    Real.sqrt_le_sqrt h34
  have himnonneg : 0 ≤ τ.im := le_of_lt τ.im_pos
  have habs : |τ.im| = τ.im := abs_of_nonneg himnonneg
  have hsq : Real.sqrt (τ.im ^ 2) = |τ.im| :=
    Real.sqrt_sq_eq_abs τ.im
  have h3_4 : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by
    -- `sqrt(3/4) = sqrt 3 / sqrt 4 = sqrt 3 / 2`.
    have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
      have h0 : (0 : ℝ) ≤ (2 : ℝ) := by positivity
      have h := Real.sqrt_sq (x := (2 : ℝ)) h0
      have hpow : ((2 : ℝ) ^ (2 : ℕ)) = (4 : ℝ) := by norm_num
      -- Rewrite the LHS `√(2^2)` into `√4`.
      simpa [hpow] using h
    calc
      Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / Real.sqrt (4 : ℝ) := by
        have h0 : (0 : ℝ) ≤ (3 : ℝ) := by positivity
        simp [Real.sqrt_div (x := (3 : ℝ)) (y := (4 : ℝ)) h0]
      _ = Real.sqrt 3 / 2 := by simp [h4]
  -- Combine.
  have : Real.sqrt (3 / 4 : ℝ) ≤ τ.im := by
    calc
      Real.sqrt (3 / 4 : ℝ) ≤ Real.sqrt (τ.im ^ 2) := hsqrt
      _ = |τ.im| := hsq
      _ = τ.im := habs
  simpa [h3_4] using this

lemma norm_q_le_exp_neg_pi_sqrt_three_of_mem_fd {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) :
    ‖q τ‖ ≤ Real.exp (-Real.pi * Real.sqrt 3) := by
  have him : Real.sqrt 3 / 2 ≤ τ.im := sqrt_three_div_two_le_im_of_mem_fd (τ := τ) hτ
  -- Use the closed-form expression for `‖qParam 1 τ‖`.
  have hnorm : ‖q τ‖ = Real.exp (-2 * Real.pi * τ.im) := by
    simpa [HeytingLean.Moonshine.Modular.q, q, Function.Periodic.qParam, div_one, mul_assoc,
      mul_left_comm, mul_comm] using
        (Function.Periodic.norm_qParam (h := (1 : ℝ)) (z := (τ : ℂ)))
  -- Since `-2π < 0`, multiplying by it reverses the inequality.
  have hneg : (-2 * Real.pi : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
  have hexp_le :
      Real.exp (-2 * Real.pi * τ.im) ≤ Real.exp (-2 * Real.pi * (Real.sqrt 3 / 2)) := by
    refine Real.exp_le_exp.mpr ?_
    -- `(-2π)*τ.im ≤ (-2π)*(sqrt3/2)` from `sqrt3/2 ≤ τ.im` and `-2π ≤ 0`.
    simpa [mul_assoc] using (mul_le_mul_of_nonpos_left him hneg)
  -- Simplify the RHS exponent: `-2π*(sqrt3/2) = -π*sqrt3`.
  have hsimp : (-2 * Real.pi * (Real.sqrt 3 / 2) : ℝ) = -Real.pi * Real.sqrt 3 := by
    ring
  -- Conclude.
  calc
    ‖q τ‖ = Real.exp (-2 * Real.pi * τ.im) := hnorm
    _ ≤ Real.exp (-2 * Real.pi * (Real.sqrt 3 / 2)) := hexp_le
    _ = Real.exp (-Real.pi * Real.sqrt 3) := congrArg Real.exp hsimp

private lemma exp_neg_pi_mul_sqrt_three_lt_one_div_hundred :
    Real.exp (-Real.pi * Real.sqrt 3) < (1 / 100 : ℝ) := by
  -- Step 1: show `5 ≤ π * √3`.
  have hpi : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  have hsqrt : (5 / 3 : ℝ) ≤ Real.sqrt 3 := by
    have hsq : (5 / 3 : ℝ) ^ (2 : ℕ) < (3 : ℝ) := by
      norm_num
    exact le_of_lt (Real.lt_sqrt_of_sq_lt hsq)
  have hfive : (5 : ℝ) ≤ Real.pi * Real.sqrt 3 := by
    nlinarith
  have hexp_le : Real.exp (-Real.pi * Real.sqrt 3) ≤ Real.exp (-5 : ℝ) := by
    refine Real.exp_le_exp.mpr ?_
    -- Negate `5 ≤ π*√3`.
    have : -(Real.pi * Real.sqrt 3) ≤ (-5 : ℝ) := by
      simpa using (neg_le_neg hfive)
    simpa [neg_mul, mul_assoc] using this
  -- Step 2: `exp (-5) < 1/100` via the explicit bound on `exp (-1)`.
  have hpow :
      Real.exp (-5 : ℝ) < (1 / 100 : ℝ) := by
    have hexp5 : Real.exp (-5 : ℝ) = Real.exp (-1 : ℝ) ^ (5 : ℕ) := by
      -- `exp (5 * (-1)) = exp (-1)^5`.
      simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.exp_nat_mul (-1 : ℝ) 5)
    have hbase : Real.exp (-1 : ℝ) < (0.3678794412 : ℝ) := Real.exp_neg_one_lt_d9
    have hpow' : Real.exp (-1 : ℝ) ^ (5 : ℕ) < (0.3678794412 : ℝ) ^ (5 : ℕ) := by
      exact pow_lt_pow_left₀ hbase (Real.exp_pos _).le (by decide : (5 : ℕ) ≠ 0)
    have hdec : (0.3678794412 : ℝ) ^ (5 : ℕ) < (1 / 100 : ℝ) := by
      norm_num
    -- Put everything together.
    have : Real.exp (-5 : ℝ) < (0.3678794412 : ℝ) ^ (5 : ℕ) := by
      simpa [hexp5] using hpow'
    exact lt_trans this hdec
  exact lt_of_le_of_lt hexp_le hpow

lemma norm_q_le_one_div_hundred_of_mem_fd {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) :
    ‖q τ‖ ≤ (1 / 100 : ℝ) := by
  have hq : ‖q τ‖ ≤ Real.exp (-Real.pi * Real.sqrt 3) :=
    norm_q_le_exp_neg_pi_sqrt_three_of_mem_fd (τ := τ) hτ
  exact hq.trans (le_of_lt exp_neg_pi_mul_sqrt_three_lt_one_div_hundred)

end HeytingLean.Moonshine.Modular
