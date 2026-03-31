/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import HeytingLean.SurrealLie.PowerSeriesExpLog

/-!
# Formal Exp/Log for Nilpotent Elements

This module defines truncated exponential and logarithm polynomials
that are exact for nilpotent elements, without requiring topology.

## Main definitions

* `expPoly N x` — truncated exponential `∑_{k=0}^{N-1} x^k / k!`
* `logPoly N y` — truncated logarithm `∑_{k=1}^{N-1} (-1)^(k-1) (y-1)^k / k`
-/

set_option autoImplicit false

open scoped BigOperators

namespace HeytingLean.SurrealLie

/-! ### Truncated Exponential -/

/-- Truncated exponential polynomial: `∑_{k=0}^{N-1} x^k / k!` -/
noncomputable def expPoly (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A] (N : ℕ) (x : A) : A :=
  ∑ k ∈ Finset.range N, ((Nat.factorial k : 𝕜)⁻¹ : 𝕜) • x ^ k

/-! ### Bridge to Mathlib's `IsNilpotent.exp` (ℚ-algebra / ℚ-module setting) -/

section NilpotentExpBridge

open IsNilpotent

variable {A : Type*} [Ring A] [Module ℚ A]

lemma expPoly_eq_nilpotentExp {x : A} {N : ℕ} (hx : x ^ N = 0) :
    expPoly ℚ A N x = IsNilpotent.exp x := by
  -- `IsNilpotent.exp_eq_sum` expands `exp` to any sufficient truncation.
  simpa [expPoly] using (IsNilpotent.exp_eq_sum (a := x) (k := N) hx).symm

lemma expPoly_mul_expPoly_neg_eq_one {x : A} {N : ℕ} (hx : x ^ N = 0) :
    expPoly ℚ A N x * expPoly ℚ A N (-x) = 1 := by
  have hx' : IsNilpotent x := ⟨N, hx⟩
  -- Rewrite to Mathlib's `IsNilpotent.exp` and use the group-like law.
  have hxneg : (-x) ^ N = 0 := by
    calc
      (-x) ^ N = (-1 : A) ^ N * x ^ N := by
        simpa using (neg_pow x N)
      _ = 0 := by
        simp [hx]
  simpa [expPoly_eq_nilpotentExp (A := A) (x := x) (N := N) hx,
    expPoly_eq_nilpotentExp (A := A) (x := -x) (N := N) hxneg] using
    (IsNilpotent.exp_mul_exp_neg_self (A := A) hx')

lemma isUnit_expPoly {x : A} {N : ℕ} (hx : x ^ N = 0) : IsUnit (expPoly ℚ A N x) := by
  have hx' : IsNilpotent x := ⟨N, hx⟩
  simpa [expPoly_eq_nilpotentExp (A := A) (x := x) (N := N) hx] using (IsNilpotent.isUnit_exp (A := A) hx')

end NilpotentExpBridge

lemma expPoly_zero_of_pos (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A] {N : ℕ} (hN : 0 < N) :
    expPoly 𝕜 A N (0 : A) = 1 := by
  classical
  -- Only the `k = 0` term survives since `0 ^ k = 0` for `k > 0`.
  simp only [expPoly]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hz : (0 : A) ^ k = 0 := by
      simpa using (zero_pow hk0 : (0 : A) ^ k = 0)
    simp [hz]
  · intro h0
    exact (h0 (Finset.mem_range.mpr hN)).elim

lemma expPoly_succ (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A] (N : ℕ) (x : A) :
    expPoly 𝕜 A (N + 1) x = expPoly 𝕜 A N x + ((Nat.factorial N : 𝕜)⁻¹ : 𝕜) • x ^ N := by
  simp only [expPoly, Finset.sum_range_succ]

lemma expPoly_two (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A] (x : A) :
    expPoly 𝕜 A 2 x = (1 : A) + x := by
  classical
  -- `range 2 = {0,1}` and `0! = 1`, `1! = 1`.
  simp [expPoly, Finset.range_add_one, add_comm]

/-- For nilpotent `x` with index ≤ `N`, higher terms vanish. -/
lemma expPoly_of_nilpotent (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A]
    {x : A} {N : ℕ} (hx : x ^ N = 0) (M : ℕ) (hM : N ≤ M) :
    expPoly 𝕜 A M x = expPoly 𝕜 A N x := by
  induction M with
  | zero =>
    simp at hM
    subst hM
    rfl
  | succ m ih =>
    cases Nat.eq_or_lt_of_le hM with
    | inl heq =>
      subst heq
      rfl
    | inr hlt =>
      rw [expPoly_succ (𝕜 := 𝕜) (A := A) m x, ih (Nat.lt_succ_iff.mp hlt)]
      have : x ^ m = 0 := by
        apply pow_eq_zero_of_le (Nat.lt_succ_iff.mp hlt) hx
      simp [this]

/-! ### Truncated Logarithm -/

/-- Truncated logarithm polynomial: `∑_{k=1}^{N-1} (-1)^(k-1) (y-1)^k / k`
    Note: We shift index so k runs from 1 to N-1. -/
noncomputable def logPoly (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A] (N : ℕ) (y : A) : A :=
  ∑ k ∈ Finset.range N,
    if k = 0 then 0
    else (((-1 : 𝕜) ^ (k - 1)) * (k : 𝕜)⁻¹ : 𝕜) • (y - 1) ^ k

@[simp] lemma logPoly_one (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A] (N : ℕ) :
    logPoly 𝕜 A N (1 : A) = 0 := by
  classical
  simp only [logPoly, sub_self]
  refine Finset.sum_eq_zero ?_
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · simp [hk0]

lemma logPoly_two (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A] (y : A) :
    logPoly 𝕜 A 2 y = y - 1 := by
  classical
  -- `range 2 = {0,1}`; the `k=0` term is `0`, and for `k=1` we get `(y-1)`.
  simp [logPoly, Finset.range_add_one, add_comm]

lemma logPoly_expPoly_two (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A] (x : A) :
    logPoly 𝕜 A 2 (expPoly 𝕜 A 2 x) = x := by
  simp [expPoly_two, logPoly_two]

lemma expPoly_logPoly_two (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A] (y : A) :
    expPoly 𝕜 A 2 (logPoly 𝕜 A 2 y) = y := by
  simp [expPoly_two, logPoly_two]

lemma logPoly_of_nilpotent (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (A : Type*) [Ring A] [Module 𝕜 A]
    {y : A} {N : ℕ} (hy : (y - 1) ^ N = 0) (M : ℕ) (hM : N ≤ M) :
    logPoly 𝕜 A M y = logPoly 𝕜 A N y := by
  classical
  induction M with
  | zero =>
    simp at hM
    subst hM
    rfl
  | succ m ih =>
    cases Nat.eq_or_lt_of_le hM with
    | inl heq =>
      subst heq
      rfl
    | inr hlt =>
      -- peel off the `m`-th term; it vanishes once `m ≥ N`.
      simp only [logPoly, Finset.sum_range_succ]
      have hm : N ≤ m := Nat.lt_succ_iff.mp hlt
      have ih' := ih hm
      -- show the new term is zero
      have hpow : (y - 1) ^ m = 0 := by
        apply pow_eq_zero_of_le hm hy
      -- The `k = 0` branch is zero, otherwise the power vanishes.
      have hz :
          (if m = 0 then (0 : A)
           else ((((-1 : 𝕜) ^ (m - 1)) * (m : 𝕜)⁻¹ : 𝕜) • (y - 1) ^ m)) = 0 := by
        by_cases hm0 : m = 0
        · subst hm0; simp
        · simp [hm0, hpow]
      simpa [ih', hz]

/-!
### Exact exp/log inverse laws (commutative `ℚ`-algebras)

Using the formal power series identities proven in `SurrealLie/PowerSeriesExpLog.lean`, we
can evaluate by substituting constant power series (which is allowed for nilpotent constants).
This yields exact inverse laws for the truncated polynomials `expPoly` and `logPoly` in the
commutative `ℚ`-algebra setting.
-/

section ExpLogInverses

open scoped BigOperators

open PowerSeries

open HeytingLean.SurrealLie.PowerSeriesExpLog

variable {A : Type*} [CommRing A] [Algebra ℚ A] [NoZeroSMulDivisors ℕ A]

private lemma hasSubst_C_of_pow_eq_zero {A : Type*} [CommRing A] {x : A} {N : ℕ}
    (hx : x ^ (N + 1) = 0) : PowerSeries.HasSubst (C x : A⟦X⟧) := by
  dsimp [PowerSeries.HasSubst]
  -- `constantCoeff (C x) = x` and `x` is nilpotent.
  simpa using (show IsNilpotent x from ⟨N + 1, hx⟩)

private lemma subst_C_eq_C_constantCoeff {A : Type*} [CommRing A]
    (f : A⟦X⟧) {x : A} (hx : IsNilpotent x) :
    f.subst (C x : A⟦X⟧) = C (PowerSeries.constantCoeff (f.subst (C x : A⟦X⟧))) := by
  classical
  have hxS : PowerSeries.HasSubst (C x : A⟦X⟧) := by
    dsimp [PowerSeries.HasSubst]
    simpa using hx
  ext n
  cases n with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
      -- All powers of `C x` are constant series, hence have zero positive coefficients.
      rw [PowerSeries.coeff_subst' hxS f (Nat.succ n)]
      have hsum :
          (∑ᶠ d : ℕ, (PowerSeries.coeff d f) • PowerSeries.coeff (Nat.succ n) ((C x : A⟦X⟧) ^ d)) =
            (0 : A) := by
        refine finsum_eq_zero_of_forall_eq_zero ?_
        intro d
        have hpow : (C x : A⟦X⟧) ^ d = C (x ^ d) :=
          (map_pow (C (R := A)) x d).symm
        rw [hpow]
        have hcoeff : PowerSeries.coeff (Nat.succ n) (C (x ^ d) : A⟦X⟧) = 0 := by
          simpa using (PowerSeries.coeff_succ_C (R := A) (a := x ^ d) (n := n))
        rw [hcoeff]
        simp
      -- The RHS coefficient is also zero.
      rw [hsum]
      simp

omit [NoZeroSMulDivisors ℕ A] in
private lemma expPoly_sub_one_pow_eq_zero {x : A} {N : ℕ} (hx : x ^ (N + 1) = 0) :
    (expPoly ℚ A (N + 1) x - 1) ^ (N + 1) = 0 := by
  classical
  -- Factor out an `x` from `expPoly - 1`, then use `x^(N+1)=0`.
  set S : A :=
    ∑ k ∈ Finset.range N, ((Nat.factorial (k + 1) : ℚ)⁻¹ : ℚ) • x ^ k
  have hfac : expPoly ℚ A (N + 1) x - 1 = x * S := by
    have h1 :
        expPoly ℚ A (N + 1) x - 1 =
          ∑ k ∈ Finset.range N, ((Nat.factorial (k + 1) : ℚ)⁻¹ : ℚ) • x ^ (k + 1) := by
      -- Split off `k = 0` and cancel the constant term.
      simp [expPoly, sub_eq_add_neg, Finset.sum_range_succ']
    have h2 :
        x * S =
          ∑ k ∈ Finset.range N, ((Nat.factorial (k + 1) : ℚ)⁻¹ : ℚ) • x ^ (k + 1) := by
      -- Distribute `x` across the sum and rewrite `x * x^k = x^(k+1)`.
      simp [S, Finset.mul_sum, pow_succ, mul_comm]
    calc
      expPoly ℚ A (N + 1) x - 1 =
          ∑ k ∈ Finset.range N, ((Nat.factorial (k + 1) : ℚ)⁻¹ : ℚ) • x ^ (k + 1) := h1
      _ = x * S := by simpa using h2.symm
  -- Raise both sides to `N+1` and use `mul_pow`.
  calc
    (expPoly ℚ A (N + 1) x - 1) ^ (N + 1) = (x * S) ^ (N + 1) := by simp [hfac]
    _ = x ^ (N + 1) * S ^ (N + 1) := by simp [mul_pow]
    _ = 0 := by simp [hx]

omit [NoZeroSMulDivisors ℕ A] in
private lemma logPoly_pow_eq_zero_of_sub_one_pow_eq_zero {y : A} {N : ℕ}
    (hy : (y - 1) ^ (N + 1) = 0) :
    (logPoly ℚ A (N + 1) y) ^ (N + 1) = 0 := by
  classical
  set t : A := y - 1
  set S : A :=
    ∑ k ∈ Finset.range N,
      ((((-1 : ℚ) ^ k) * ((k + 1 : ℕ) : ℚ)⁻¹ : ℚ) • t ^ k)
  have hfac : logPoly ℚ A (N + 1) y = t * S := by
    have h1 :
        logPoly ℚ A (N + 1) y =
          ∑ k ∈ Finset.range N,
            ((((-1 : ℚ) ^ k) * ((k + 1 : ℕ) : ℚ)⁻¹ : ℚ) • t ^ (k + 1)) := by
      -- Split off `k = 0` and shift the index.
      simp [logPoly, t, Finset.sum_range_succ']
    have h2 :
        t * S =
          ∑ k ∈ Finset.range N,
            ((((-1 : ℚ) ^ k) * ((k + 1 : ℕ) : ℚ)⁻¹ : ℚ) • t ^ (k + 1)) := by
      -- Distribute `t` across the sum and rewrite `t * t^k = t^(k+1)`.
      simp [S, Finset.mul_sum, pow_succ, mul_comm]
    calc
      logPoly ℚ A (N + 1) y =
          ∑ k ∈ Finset.range N,
            ((((-1 : ℚ) ^ k) * ((k + 1 : ℕ) : ℚ)⁻¹ : ℚ) • t ^ (k + 1)) := h1
      _ = t * S := by simpa using h2.symm
  calc
    (logPoly ℚ A (N + 1) y) ^ (N + 1) = (t * S) ^ (N + 1) := by simp [hfac]
    _ = t ^ (N + 1) * S ^ (N + 1) := by simp [mul_pow]
    _ = 0 := by simp [t, hy]

omit [NoZeroSMulDivisors ℕ A] in
private lemma constantCoeff_exp_subst_C_eq_expPoly {x : A} {N : ℕ} (hx : x ^ (N + 1) = 0) :
    PowerSeries.constantCoeff ((PowerSeries.exp A).subst (C x : A⟦X⟧)) =
      expPoly ℚ A (N + 1) x := by
  classical
  have hxS : PowerSeries.HasSubst (C x : A⟦X⟧) := hasSubst_C_of_pow_eq_zero (A := A) (N := N) hx
  -- Use the constant coefficient formula for substitution; only finitely many powers survive.
  have hconstMv := PowerSeries.constantCoeff_subst (R := A) (a := (C x : A⟦X⟧)) hxS (f := PowerSeries.exp A)
  have hconst :
      PowerSeries.constantCoeff ((PowerSeries.exp A).subst (C x : A⟦X⟧)) =
        ∑ᶠ d : ℕ, (PowerSeries.coeff d (PowerSeries.exp A)) • PowerSeries.constantCoeff ((C x : A⟦X⟧) ^ d) := by
    simpa [PowerSeries.constantCoeff] using hconstMv
  -- Reduce the `finsum` to `range (N+1)` since `x^(N+1)=0`.
  have hsub :
      (fun d : ℕ => (PowerSeries.coeff d (PowerSeries.exp A)) • x ^ d).support ⊆
        (Finset.range (N + 1) : Finset ℕ) := by
    intro d hd
    by_contra hmem
    have hdle : N + 1 ≤ d := by
      have : ¬d < N + 1 := by simpa [Finset.mem_range] using hmem
      exact Nat.le_of_not_gt this
    have : x ^ d = 0 := pow_eq_zero_of_le hdle hx
    have : (PowerSeries.coeff d (PowerSeries.exp A)) • x ^ d = 0 := by simp [this]
    exact hd (by simpa [Function.mem_support, this])
  -- Rewrite using `finsum_eq_sum_of_support_subset` and identify coefficients of `exp`.
  rw [hconst]
  -- `constantCoeff ((C x)^d) = x^d`
  simp only [PowerSeries.constantCoeff_C, map_pow, smul_eq_mul] at *
  -- turn `finsum` into a finite sum
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (N + 1))
    (fun d : ℕ => PowerSeries.coeff d (PowerSeries.exp A) * x ^ d) hsub]
  -- `coeff d exp = algebraMap (1 / d!)`
  simp [expPoly, PowerSeries.coeff_exp, Algebra.smul_def, one_div]

omit [NoZeroSMulDivisors ℕ A] in
private lemma constantCoeff_log1p_subst_C_eq_logPoly {t : A} {N : ℕ} (ht : t ^ (N + 1) = 0) :
    PowerSeries.constantCoeff ((PowerSeriesExpLog.log1p (R := A)).subst (C t : A⟦X⟧)) =
      logPoly ℚ A (N + 1) (1 + t) := by
  classical
  have htS : PowerSeries.HasSubst (C t : A⟦X⟧) := by
    dsimp [PowerSeries.HasSubst]
    simpa using (show IsNilpotent t from ⟨N + 1, ht⟩)
  have hconstMv := PowerSeries.constantCoeff_subst (R := A) (a := (C t : A⟦X⟧)) htS
    (f := PowerSeriesExpLog.log1p (R := A))
  have hconst :
      PowerSeries.constantCoeff ((PowerSeriesExpLog.log1p (R := A)).subst (C t : A⟦X⟧)) =
        ∑ᶠ d : ℕ,
          (PowerSeries.coeff d (PowerSeriesExpLog.log1p (R := A))) •
            PowerSeries.constantCoeff ((C t : A⟦X⟧) ^ d) := by
    simpa [PowerSeries.constantCoeff] using hconstMv
  have hsub :
      (fun d : ℕ => (PowerSeries.coeff d (PowerSeriesExpLog.log1p (R := A))) • t ^ d).support ⊆
        (Finset.range (N + 1) : Finset ℕ) := by
    intro d hd
    by_contra hmem
    have hdle : N + 1 ≤ d := by
      have : ¬d < N + 1 := by simpa [Finset.mem_range] using hmem
      exact Nat.le_of_not_gt this
    have : t ^ d = 0 := pow_eq_zero_of_le hdle ht
    have : (PowerSeries.coeff d (PowerSeriesExpLog.log1p (R := A))) • t ^ d = 0 := by simp [this]
    exact hd (by simpa [Function.mem_support, this])
  rw [hconst]
  simp only [PowerSeries.constantCoeff_C, map_pow, smul_eq_mul] at *
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (N + 1))
    (fun d : ℕ => PowerSeries.coeff d (PowerSeriesExpLog.log1p (R := A)) * t ^ d) hsub]
  -- Identify the coefficients with the definition of `logPoly`.
  simp [PowerSeriesExpLog.log1p, logPoly, sub_eq_add_neg, Algebra.smul_def, div_eq_mul_inv]

theorem logPoly_expPoly_of_pow_eq_zero {x : A} {N : ℕ} (hx : x ^ (N + 1) = 0) :
    logPoly ℚ A (N + 1) (expPoly ℚ A (N + 1) x) = x := by
  classical
  have hxS : PowerSeries.HasSubst (C x : A⟦X⟧) :=
    hasSubst_C_of_pow_eq_zero (A := A) (N := N) hx
  have ha : PowerSeries.HasSubst ((PowerSeries.exp A : A⟦X⟧) - 1) := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    simp [PowerSeries.constantCoeff_exp]
  -- Substitute `X ↦ C x` into `log1p ∘ (exp-1) = X` and take constant coefficients.
  have hcc :=
    congrArg PowerSeries.constantCoeff
      (congrArg (PowerSeries.subst (C x : A⟦X⟧))
        (PowerSeriesExpLog.log1p_subst_exp_sub_one (R := A)))
  -- RHS is `x`.
  have hR : PowerSeries.constantCoeff ((X : A⟦X⟧).subst (C x : A⟦X⟧)) = x := by
    -- `subst (C x) X = C x`.
    simpa using congrArg PowerSeries.constantCoeff (PowerSeries.subst_X (R := A) (a := (C x : A⟦X⟧)) hxS)
  -- Compute the substituted inner series `(exp-1)(x)` as a constant series.
  set t : A := expPoly ℚ A (N + 1) x - 1
  have ht : t ^ (N + 1) = 0 := by
    simpa [t] using expPoly_sub_one_pow_eq_zero (A := A) (x := x) (N := N) hx
  have hxNil : IsNilpotent x := ⟨N + 1, hx⟩
  have hExpSubOne : PowerSeries.subst (C x : A⟦X⟧) ((PowerSeries.exp A : A⟦X⟧) - 1) = C t := by
    have hccSub :
        PowerSeries.constantCoeff (PowerSeries.subst (C x : A⟦X⟧) ((PowerSeries.exp A : A⟦X⟧) - 1)) = t := by
      -- Use `substAlgHom` to access `map_sub`.
      have hsubexp :
          (PowerSeries.substAlgHom hxS) (PowerSeries.exp A) =
            PowerSeries.subst (C x : A⟦X⟧) (PowerSeries.exp A) :=
        congrArg (fun g => g (PowerSeries.exp A)) (PowerSeries.coe_substAlgHom (R := A) (a := (C x : A⟦X⟧)) hxS)
      have hsubsub :
          (PowerSeries.substAlgHom hxS) ((PowerSeries.exp A : A⟦X⟧) - 1) =
            PowerSeries.subst (C x : A⟦X⟧) ((PowerSeries.exp A : A⟦X⟧) - 1) :=
        congrArg (fun g => g ((PowerSeries.exp A : A⟦X⟧) - 1))
          (PowerSeries.coe_substAlgHom (R := A) (a := (C x : A⟦X⟧)) hxS)
      have hmap' :
          PowerSeries.subst (C x : A⟦X⟧) ((PowerSeries.exp A : A⟦X⟧) - 1) =
            PowerSeries.subst (C x : A⟦X⟧) (PowerSeries.exp A) - 1 := by
        -- `substAlgHom` is an `AlgHom`, so it respects subtraction and sends `1` to `1`.
        have hmap := (PowerSeries.substAlgHom hxS).map_sub (PowerSeries.exp A) (1 : A⟦X⟧)
        simpa [hsubsub, hsubexp] using hmap
      have hccMap := congrArg PowerSeries.constantCoeff hmap'
      -- Evaluate the constant coefficient using the exp evaluation lemma.
      simpa [t, constantCoeff_exp_subst_C_eq_expPoly (A := A) (x := x) (N := N) hx] using hccMap
    -- Substituting a constant series yields a constant series.
    simpa [hccSub] using
      (subst_C_eq_C_constantCoeff (A := A) ((PowerSeries.exp A : A⟦X⟧) - 1) (x := x) hxNil)
  have hLseries :
      PowerSeries.subst (C x : A⟦X⟧)
          (PowerSeries.subst ((PowerSeries.exp A : A⟦X⟧) - 1) (PowerSeriesExpLog.log1p (R := A))) =
        PowerSeries.subst (C t : A⟦X⟧) (PowerSeriesExpLog.log1p (R := A)) := by
    have hcomp :=
      PowerSeries.subst_comp_subst_apply (R := A) (a := ((PowerSeries.exp A : A⟦X⟧) - 1))
        (b := (C x : A⟦X⟧)) ha hxS (f := PowerSeriesExpLog.log1p (R := A))
    simpa [hExpSubOne] using hcomp
  have hL :
      PowerSeries.constantCoeff
        (PowerSeries.subst (C x : A⟦X⟧)
          (PowerSeries.subst ((PowerSeries.exp A : A⟦X⟧) - 1) (PowerSeriesExpLog.log1p (R := A)))) =
        logPoly ℚ A (N + 1) (expPoly ℚ A (N + 1) x) := by
    -- Reduce to evaluating `log1p` at the nilpotent constant `t`.
    rw [hLseries]
    -- `1 + t = expPoly ... x`.
    simpa [t, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (constantCoeff_log1p_subst_C_eq_logPoly (A := A) (t := t) (N := N) ht)
  -- Finish by comparing constant coefficients.
  simpa [hL, hR] using hcc

theorem expPoly_logPoly_of_sub_one_pow_eq_zero {y : A} {N : ℕ} (hy : (y - 1) ^ (N + 1) = 0) :
    expPoly ℚ A (N + 1) (logPoly ℚ A (N + 1) y) = y := by
  classical
  set t : A := y - 1
  have ht : t ^ (N + 1) = 0 := by simpa [t] using hy
  have htS : PowerSeries.HasSubst (C t : A⟦X⟧) :=
    hasSubst_C_of_pow_eq_zero (A := A) (N := N) ht
  have ha : PowerSeries.HasSubst (PowerSeriesExpLog.log1p (R := A)) := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    exact PowerSeriesExpLog.constantCoeff_log1p (R := A)
  -- Substitute `X ↦ C t` into `exp ∘ log1p = 1 + X` and take constant coefficients.
  have hcc :=
    congrArg PowerSeries.constantCoeff
      (congrArg (PowerSeries.subst (C t : A⟦X⟧)) (PowerSeriesExpLog.exp_subst_log1p (R := A)))
  have honeSeries : PowerSeries.subst (C t : A⟦X⟧) (1 : A⟦X⟧) = (1 : A⟦X⟧) := by
    simpa using
      (PowerSeries.subst_coe (R := A) (a := (C t : A⟦X⟧)) htS (p := (1 : Polynomial A)))
  have hXSeries : PowerSeries.subst (C t : A⟦X⟧) (X : A⟦X⟧) = (C t : A⟦X⟧) := by
    simpa using (PowerSeries.subst_X (R := A) (a := (C t : A⟦X⟧)) htS)
  have hRseries :
      PowerSeries.subst (C t : A⟦X⟧) ((1 : A⟦X⟧) + (X : A⟦X⟧)) = (1 : A⟦X⟧) + C t := by
    simpa [honeSeries, hXSeries] using
      (PowerSeries.subst_add (R := A) (a := (C t : A⟦X⟧)) htS (f := (1 : A⟦X⟧)) (g := (X : A⟦X⟧)))
  have hR : PowerSeries.constantCoeff (PowerSeries.subst (C t : A⟦X⟧) (1 + (X : A⟦X⟧))) = y := by
    -- `constantCoeff (1 + C t) = 1 + t = y`.
    have : PowerSeries.constantCoeff (PowerSeries.subst (C t : A⟦X⟧) ((1 : A⟦X⟧) + (X : A⟦X⟧))) =
        (1 : A) + t := by
      simp [hRseries]
    simpa [t, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  -- Evaluate `log1p` at `t` as a constant series.
  set u : A := logPoly ℚ A (N + 1) y
  have hu : PowerSeries.subst (C t : A⟦X⟧) (PowerSeriesExpLog.log1p (R := A)) = C u := by
    have hcu :
        PowerSeries.constantCoeff (PowerSeries.subst (C t : A⟦X⟧) (PowerSeriesExpLog.log1p (R := A))) = u := by
      -- `1 + t = y`.
      simpa [u, t, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (constantCoeff_log1p_subst_C_eq_logPoly (A := A) (t := t) (N := N) ht)
    -- Substituting a constant series yields a constant series.
    simpa [hcu] using
      (subst_C_eq_C_constantCoeff (A := A) (PowerSeriesExpLog.log1p (R := A)) (x := t) ⟨N + 1, ht⟩)
  have huNil : u ^ (N + 1) = 0 := by
    simpa [u] using logPoly_pow_eq_zero_of_sub_one_pow_eq_zero (A := A) (y := y) (N := N) hy
  have hcomp :
      PowerSeries.subst (C t : A⟦X⟧)
          (PowerSeries.subst (PowerSeriesExpLog.log1p (R := A)) (PowerSeries.exp A)) =
        PowerSeries.subst (C u : A⟦X⟧) (PowerSeries.exp A) := by
    have hcomp' :=
      PowerSeries.subst_comp_subst_apply (R := A) (a := PowerSeriesExpLog.log1p (R := A))
        (b := (C t : A⟦X⟧)) ha htS (f := PowerSeries.exp A)
    simpa [hu] using hcomp'
  have hL :
      PowerSeries.constantCoeff
        (PowerSeries.subst (C t : A⟦X⟧)
          (PowerSeries.subst (PowerSeriesExpLog.log1p (R := A)) (PowerSeries.exp A))) =
        expPoly ℚ A (N + 1) u := by
    rw [hcomp]
    simpa using (constantCoeff_exp_subst_C_eq_expPoly (A := A) (x := u) (N := N) huNil)
  -- Finish by comparing constant coefficients.
  have : expPoly ℚ A (N + 1) u = y := by
    simpa [hL, hR] using hcc
  simpa [u] using this

end ExpLogInverses

end HeytingLean.SurrealLie
