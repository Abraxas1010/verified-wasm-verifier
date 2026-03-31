/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Power Series Exp/Log(1+X) Infrastructure

This file provides a formal power series `log1p` (the logarithm series of `1 + X`) and
auxiliary lemmas intended to support topology-free exp/log inverse results for nilpotent
elements in `ℚ`-algebras.

Theorems are stated in a way that does not require analytic topology; they live in the
algebraic power series ring.
-/

set_option autoImplicit false

namespace HeytingLean.SurrealLie

namespace PowerSeriesExpLog

open scoped BigOperators

open PowerSeries

section CommRing

variable {R : Type*} [CommRing R]

/-!
## A formal inverse for `(1 + X)`

The geometric series `1 - X + X^2 - ...` is `1 / (1 + X)` in `R⟦X⟧`.
-/

/-- The formal power series for `1 / (1 + X)`: `∑_{n≥0} (-1)^n X^n`. -/
noncomputable def invOneAddX : PowerSeries R :=
  PowerSeries.evalNegHom (PowerSeries.mk (fun _ : ℕ => (1 : R)))

@[simp] theorem coeff_invOneAddX (n : ℕ) :
    PowerSeries.coeff n (invOneAddX (R := R)) = (-1 : R) ^ n := by
  -- `evalNegHom` is `rescale (-1)`.
  simp [invOneAddX, PowerSeries.evalNegHom, PowerSeries.coeff_rescale]

@[simp] theorem constantCoeff_invOneAddX :
    PowerSeries.constantCoeff (invOneAddX (R := R)) = 1 := by
  have h : PowerSeries.coeff 0 (invOneAddX (R := R)) = 1 := by
    simp [coeff_invOneAddX]
  exact (PowerSeries.coeff_zero_eq_constantCoeff_apply (φ := invOneAddX (R := R))).symm.trans h

theorem invOneAddX_mul_one_add_X :
    invOneAddX (R := R) * (1 + (X : R⟦X⟧)) = 1 := by
  -- Start from `(1 + X + X^2 + ...) * (1 - X) = 1` and substitute `X ↦ -X`.
  have h := PowerSeries.mk_one_mul_one_sub_eq_one (S := R)
  have h' := congrArg (PowerSeries.evalNegHom (A := R)) h
  -- Simplify `evalNegHom (1 - X) = 1 + X` in a controlled way (avoids simp recursion depth).
  have he : PowerSeries.evalNegHom (A := R) (1 - (X : R⟦X⟧)) = (1 : R⟦X⟧) + X := by
    simp [sub_eq_add_neg, PowerSeries.evalNegHom_X]
  -- Now finish.
  simpa [invOneAddX, map_mul, he] using h'

theorem one_add_X_mul_invOneAddX :
    (1 + (X : R⟦X⟧)) * invOneAddX (R := R) = 1 := by
  simpa [mul_comm] using (invOneAddX_mul_one_add_X (R := R))

noncomputable def oneAddXUnit : (R⟦X⟧)ˣ where
  val := 1 + (X : R⟦X⟧)
  inv := invOneAddX (R := R)
  val_inv := by
    simpa [mul_assoc] using (one_add_X_mul_invOneAddX (R := R))
  inv_val := by
    simpa [mul_assoc] using (invOneAddX_mul_one_add_X (R := R))

/-!
## A coefficient formula for `subst` when `constantCoeff` is zero
-/

private theorem coeff_pow_eq_zero_of_constantCoeff_eq_zero
    {g : R⟦X⟧} (hg0 : PowerSeries.constantCoeff g = 0) {n k : ℕ} (h : n < k) :
    PowerSeries.coeff n (g ^ k) = 0 := by
  -- Split off the constant coefficient: `g = shift * X` since `constantCoeff g = 0`.
  have hgX :
      g = (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) g) * (X : R⟦X⟧) := by
    simpa [hg0] using (PowerSeries.eq_shift_mul_X_add_const (φ := g))
  -- Then `g^k` has a factor `X^k`, so its coefficients below `k` vanish.
  -- Rewrite the power and extract an `X^k` factor.
  have hk : ¬k ≤ n := Nat.not_le_of_gt h
  -- `rw` avoids `simp` recursion depth issues.
  rw [hgX]
  -- Now `g` is literally `shift * X`.
  simp [mul_pow, PowerSeries.coeff_mul_X_pow', hk]

theorem coeff_subst_eq_sum_range_of_constantCoeff_eq_zero
    {f g : R⟦X⟧} (hg0 : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst g) =
      ∑ d ∈ Finset.range (n + 1),
        (PowerSeries.coeff d f) • PowerSeries.coeff n (g ^ d) := by
  classical
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  have hsub :
      (fun d : ℕ => (PowerSeries.coeff d f) • PowerSeries.coeff n (g ^ d)).support
        ⊆ (Finset.range (n + 1) : Finset ℕ) := by
    intro d hd
    by_contra hmem
    have hdn : n < d := by
      have : ¬d < n + 1 := by simpa [Finset.mem_range] using hmem
      have hdle : n + 1 ≤ d := Nat.le_of_not_gt this
      exact lt_of_lt_of_le (Nat.lt_succ_self n) hdle
    have hz : PowerSeries.coeff n (g ^ d) = 0 :=
      coeff_pow_eq_zero_of_constantCoeff_eq_zero (R := R) hg0 hdn
    have : (PowerSeries.coeff d f) • PowerSeries.coeff n (g ^ d) = 0 := by
      simp [hz]
    exact hd (by simpa [Function.mem_support, this])
  -- Replace the `finsum` by a finite sum.
  -- `coeff_subst'` is the `finsum` coefficient formula for substitution.
  rw [PowerSeries.coeff_subst' hgs f n]
  simpa using (finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))
    (fun d : ℕ => (PowerSeries.coeff d f) • PowerSeries.coeff n (g ^ d)) hsub)

theorem constantCoeff_subst_of_constantCoeff_eq_zero
    {f g : R⟦X⟧} (hg0 : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff (f.subst g) = PowerSeries.constantCoeff f := by
  -- Use the coefficient formula at `n = 0`: only the `d = 0` term survives.
  have h0 := coeff_subst_eq_sum_range_of_constantCoeff_eq_zero (R := R) (f := f) (g := g) hg0 0
  have : PowerSeries.coeff 0 (f.subst g) = PowerSeries.coeff 0 f := by
    -- `range 1 = {0}` and `g^0 = 1`.
    simpa [Finset.range_one, pow_zero] using h0
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using this

/-!
## Chain rule for `PowerSeries.subst` (inner constant term `0`)

This is proved coefficientwise by reducing to polynomial truncations and using the
polynomial chain rule for the derivation `d⁄dX`.
-/

private theorem derivative_subst_coe_polynomial
    {p : Polynomial R} {g : R⟦X⟧} (hg : PowerSeries.HasSubst g) :
    d⁄dX R ((p : R⟦X⟧).subst g) =
      (d⁄dX R (p : R⟦X⟧)).subst g * d⁄dX R g := by
  simp [PowerSeries.subst_coe hg, PowerSeries.derivative_coe, smul_eq_mul]

theorem derivative_subst_of_constantCoeff_eq_zero
    {f g : R⟦X⟧} (hg0 : PowerSeries.constantCoeff g = 0) :
    d⁄dX R (f.subst g) = (d⁄dX R f).subst g * d⁄dX R g := by
  classical
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  ext n
  -- Truncate `f` to a polynomial capturing coefficients up to `n+1`.
  let p : Polynomial R := PowerSeries.trunc (n + 2) f
  have hp (d : ℕ) (hd : d < n + 2) :
      PowerSeries.coeff d (p : R⟦X⟧) = PowerSeries.coeff d f := by
    simpa [p] using (PowerSeries.coeff_coe_trunc_of_lt (R := R) (f := f) hd)
  -- LHS coefficient: reduce to the truncated polynomial `p`.
  have hL :
      PowerSeries.coeff n (d⁄dX R (f.subst g)) =
        PowerSeries.coeff n (d⁄dX R ((p : R⟦X⟧).subst g)) := by
    -- It suffices to compare `coeff (n+1)` of the substituted series.
    have hs :
        PowerSeries.coeff (n + 1) (f.subst g) =
          PowerSeries.coeff (n + 1) ((p : R⟦X⟧).subst g) := by
      have hs1 :=
        coeff_subst_eq_sum_range_of_constantCoeff_eq_zero (R := R) (f := f) (g := g) hg0 (n := n + 1)
      have hs2 :=
        coeff_subst_eq_sum_range_of_constantCoeff_eq_zero (R := R) (f := (p : R⟦X⟧)) (g := g) hg0 (n := n + 1)
      rw [hs1, hs2]
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hd' : d < n + 2 := by
        simpa [Finset.mem_range, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
      simp [hp d hd']
    simp [PowerSeries.coeff_derivative, hs]
  -- RHS coefficient: reduce to the truncated polynomial `p` in the first factor, up to `n`.
  have hR :
      PowerSeries.coeff n ((d⁄dX R f).subst g * d⁄dX R g) =
        PowerSeries.coeff n ((d⁄dX R (p : R⟦X⟧)).subst g * d⁄dX R g) := by
    -- Reduce coefficient of a product to truncations of length `n+1`.
    have hn : n < n + 1 := Nat.lt_succ_self n
    rw [PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc (R := R) (f := (d⁄dX R f).subst g)
      (g := d⁄dX R g) hn]
    rw [PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc (R := R) (f := (d⁄dX R (p : R⟦X⟧)).subst g)
      (g := d⁄dX R g) hn]
    -- It remains to show the truncations of the first factor agree.
    have htrunc :
        PowerSeries.trunc (n + 1) ((d⁄dX R f).subst g) =
          PowerSeries.trunc (n + 1) ((d⁄dX R (p : R⟦X⟧)).subst g) := by
      ext m
      simp only [PowerSeries.coeff_trunc]
      by_cases hm : m < n + 1
      · -- Compare coefficients `< n+1` via the finite substitution formula.
        have hs1 :=
          coeff_subst_eq_sum_range_of_constantCoeff_eq_zero (R := R) (f := d⁄dX R f) (g := g) hg0 (n := m)
        have hs2 :=
          coeff_subst_eq_sum_range_of_constantCoeff_eq_zero (R := R) (f := d⁄dX R (p : R⟦X⟧)) (g := g) hg0 (n := m)
        rw [if_pos hm, if_pos hm, hs1, hs2]
        refine Finset.sum_congr rfl ?_
        intro d hd
        -- Use `coeff_derivative` and the fact that `p` matches `f` up to `m+1 ≤ n+1`.
        have hdm : d < m + 1 := by simpa [Finset.mem_range] using hd
        have hd' : d + 1 < n + 2 := by
          have : d + 1 ≤ m + 1 := Nat.succ_le_succ (Nat.le_of_lt_succ hdm)
          have hm' : m + 1 ≤ n + 1 := Nat.succ_le_of_lt hm
          have : d + 1 ≤ n + 1 := le_trans this hm'
          exact lt_of_le_of_lt this (Nat.lt_succ_self (n + 1))
        have hder :
            PowerSeries.coeff d (d⁄dX R f) =
              PowerSeries.coeff d (d⁄dX R (p : R⟦X⟧)) := by
          simp [PowerSeries.coeff_derivative, hp (d + 1) (by simpa [Nat.add_assoc] using hd')]
        simp [hder]
      · -- Both coefficients are truncated to `0`.
        simp [hm]
    simp [htrunc]
  -- Use the polynomial chain rule at coefficient `n`.
  have hpoly :
      d⁄dX R ((p : R⟦X⟧).subst g) =
        (d⁄dX R (p : R⟦X⟧)).subst g * d⁄dX R g :=
    derivative_subst_coe_polynomial (R := R) (p := p) (g := g) hgs
  simpa [hL, hR] using congrArg (PowerSeries.coeff n) hpoly

end CommRing

section QAlg

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-! ### The logarithm series `log(1+X)` -/

/-- The formal power series for `log(1+X)`: `∑_{n≥1} (-1)^(n-1) X^n / n`. -/
noncomputable def log1p : PowerSeries R :=
  PowerSeries.mk fun n : ℕ =>
    if n = 0 then 0 else algebraMap ℚ R (((-1 : ℚ) ^ (n - 1)) / (n : ℚ))

@[simp] theorem constantCoeff_log1p :
    PowerSeries.constantCoeff (log1p (R := R)) = 0 := by
  simp [log1p]

/-! ### Derivatives of `exp` and `log1p` -/

theorem derivative_exp :
    d⁄dX R (PowerSeries.exp R) = (PowerSeries.exp R) := by
  ext n
  -- Reduce to an equality in `ℚ` and then map into `R`.
  have hn : (n + 1 : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hq :
      ((1 : ℚ) / (Nat.factorial (n + 1) : ℚ)) * (n + 1 : ℚ) =
        (1 : ℚ) / (Nat.factorial n : ℚ) := by
    -- `(n+1)! = (n+1) * n!` and cancel.
    simp [Nat.factorial_succ, div_eq_mul_inv, mul_left_comm, mul_comm, hn]
  -- Compare coefficients via `coeff_derivative` and `coeff_exp`.
  simpa [PowerSeries.coeff_derivative, PowerSeries.coeff_exp, map_mul, hq, mul_comm, mul_left_comm] using
    congrArg (algebraMap ℚ R) hq

theorem derivative_log1p :
    d⁄dX R (log1p (R := R)) = invOneAddX (R := R) := by
  ext n
  have hn : (n + 1 : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hq :
      (((-1 : ℚ) ^ n) / (n + 1 : ℚ)) * (n + 1 : ℚ) = ((-1 : ℚ) ^ n) := by
    simp [div_eq_mul_inv, hn]
  have hqR := congrArg (algebraMap ℚ R) hq
  have hnat : algebraMap ℚ R (n + 1 : ℚ) = (n + 1 : R) := by
    simp
  -- Now compute both coefficients.
  -- LHS coefficient: `coeff (n+1) log1p * (n+1)`.
  -- Coefficient computation for the derivative.
  have hmul :
      (algebraMap ℚ R (((-1 : ℚ) ^ n) / (n + 1 : ℚ))) * (n + 1 : R) =
        algebraMap ℚ R ((-1 : ℚ) ^ n) := by
    -- reorder to match `hqR`
    simpa [map_mul, hnat, mul_assoc, mul_comm, mul_left_comm] using hqR
  -- Now compare coefficients.
  have hcoeff : PowerSeries.coeff n (d⁄dX R (log1p (R := R))) = (-1 : R) ^ n := by
    -- Unfold `coeff_derivative` and `log1p`, then use `hmul`.
    simp [PowerSeries.coeff_derivative, log1p, hmul]
  -- RHS coefficient: `invOneAddX` has coefficient `(-1)^n`.
  simpa [invOneAddX, PowerSeries.evalNegHom, PowerSeries.coeff_rescale] using hcoeff

/-!
## The core exp/log1p identities in `R⟦X⟧`
-/

variable [NoZeroSMulDivisors ℕ R]

theorem exp_subst_log1p :
    (PowerSeries.exp R).subst (log1p (R := R)) = 1 + (X : R⟦X⟧) := by
  -- Let `E := exp ∘ log1p`. Show `E * (1+X)⁻¹ = 1` by differentiation.
  let E : R⟦X⟧ := (PowerSeries.exp R).subst (log1p (R := R))
  have hlog : PowerSeries.constantCoeff (log1p (R := R)) = 0 := constantCoeff_log1p (R := R)
  have hE' : d⁄dX R E = E * invOneAddX (R := R) := by
    have := derivative_subst_of_constantCoeff_eq_zero (R := R) (f := PowerSeries.exp R)
      (g := log1p (R := R)) hlog
    simpa [E, derivative_exp (R := R), derivative_log1p (R := R), mul_assoc] using this
  let K : R⟦X⟧ := E * invOneAddX (R := R)
  have hInv' : d⁄dX R (invOneAddX (R := R)) = -(invOneAddX (R := R)) ^ 2 := by
    -- `invOneAddX` is the inverse of the unit `1+X`.
    simpa [oneAddXUnit, PowerSeries.derivative_C, PowerSeries.derivative_X, pow_two, mul_assoc] using
      (PowerSeries.derivative_inv (R := R) (f := oneAddXUnit (R := R)))
  have hK' : d⁄dX R K = 0 := by
    -- Differentiate `K` and simplify using `hE'` and `hInv'`.
    -- The cancellation is purely algebraic: `E * inv^2 - E * inv^2 = 0`.
    simp [K, Derivation.leibniz, hE', hInv', pow_two, mul_assoc, mul_comm]
  have hKc : PowerSeries.constantCoeff K = 1 := by
    have hEconst : PowerSeries.constantCoeff E = 1 := by
      simpa [E, PowerSeries.constantCoeff_exp] using
        (constantCoeff_subst_of_constantCoeff_eq_zero (R := R) (f := PowerSeries.exp R)
          (g := log1p (R := R)) hlog)
    simp [K, hEconst, constantCoeff_invOneAddX (R := R)]
  have hK : K = 1 := by
    have hD : d⁄dX R K = d⁄dX R (1 : R⟦X⟧) := by simpa using hK'
    have hc : PowerSeries.constantCoeff K = PowerSeries.constantCoeff (1 : R⟦X⟧) := by
      simp [hKc]
    exact PowerSeries.derivative.ext (R := R) hD hc
  -- From `E * invOneAddX = 1`, deduce `E = 1 + X`.
  have hunit : invOneAddX (R := R) * (1 + (X : R⟦X⟧)) = 1 := invOneAddX_mul_one_add_X (R := R)
  calc
    E = (E * invOneAddX (R := R)) * (1 + (X : R⟦X⟧)) := by
          simp [mul_assoc, hunit]
    _ = 1 * (1 + (X : R⟦X⟧)) := by
          simpa [K, E] using congrArg (fun t => t * (1 + (X : R⟦X⟧))) hK
    _ = 1 + (X : R⟦X⟧) := by simp

theorem log1p_subst_exp_sub_one :
    (log1p (R := R)).subst ((PowerSeries.exp R) - 1) = (X : R⟦X⟧) := by
  have hinner : PowerSeries.constantCoeff ((PowerSeries.exp R : R⟦X⟧) - 1) = 0 := by
    simp [PowerSeries.constantCoeff_exp]
  have hder :
      d⁄dX R ((log1p (R := R)).subst ((PowerSeries.exp R) - 1)) = 1 := by
    have := derivative_subst_of_constantCoeff_eq_zero (R := R) (f := log1p (R := R))
      (g := (PowerSeries.exp R) - 1) hinner
    have hexp : d⁄dX R ((PowerSeries.exp R : R⟦X⟧) - 1) = (PowerSeries.exp R) := by
      simp [derivative_exp (R := R)]
    have hgs : PowerSeries.HasSubst ((PowerSeries.exp R : R⟦X⟧) - 1) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hinner
    have hinv :
        (invOneAddX (R := R)).subst ((PowerSeries.exp R : R⟦X⟧) - 1) * (PowerSeries.exp R) = 1 := by
      -- Substitute into `invOneAddX * (1+X) = 1`.
      have hbase : invOneAddX (R := R) * (1 + (X : R⟦X⟧)) = 1 :=
        invOneAddX_mul_one_add_X (R := R)
      have hsub := congrArg (PowerSeries.substAlgHom hgs) hbase
      -- `substAlgHom` is an `AlgHom`; simplify `subst (1 + X)` to `exp`.
      have hsub' :
          (PowerSeries.substAlgHom hgs) (invOneAddX (R := R)) *
              (PowerSeries.substAlgHom hgs) ((1 : R⟦X⟧) + (X : R⟦X⟧)) = 1 := by
        simpa [map_mul, map_one] using hsub
      -- Convert back to `.subst` and simplify.
      -- Since `substAlgHom` sends `X` to `exp - 1`, it sends `1 + X` to `exp`.
      simpa [PowerSeries.coe_substAlgHom, PowerSeries.substAlgHom_X, map_add, map_one, map_sub,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub'
    -- Chain rule: `((log1p)' ∘ (exp-1)) * (exp-1)' = (invOneAddX ∘ (exp-1)) * exp = 1`.
    simpa [derivative_log1p (R := R), hexp, hinv, mul_assoc] using this
  have hconst :
      PowerSeries.constantCoeff ((log1p (R := R)).subst ((PowerSeries.exp R) - 1)) =
        PowerSeries.constantCoeff (X : R⟦X⟧) := by
    -- Inner has constant term `0`, so constantCoeff of substitution is constantCoeff of `log1p`.
    simpa [PowerSeries.constantCoeff_X, constantCoeff_log1p (R := R)] using
      (constantCoeff_subst_of_constantCoeff_eq_zero (R := R) (f := log1p (R := R))
        (g := (PowerSeries.exp R : R⟦X⟧) - 1) hinner)
  have hD : d⁄dX R ((log1p (R := R)).subst ((PowerSeries.exp R) - 1)) =
      d⁄dX R (X : R⟦X⟧) := by
    simpa [PowerSeries.derivative_X] using hder
  exact PowerSeries.derivative.ext (R := R) hD hconst

end QAlg

end PowerSeriesExpLog

end HeytingLean.SurrealLie
