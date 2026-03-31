import HeytingLean.Moonshine.Modular.Eisenstein
import HeytingLean.Moonshine.Modular.EisensteinExpectedQExpansion
import HeytingLean.Moonshine.Modular.KleinCuspFunction
import HeytingLean.Moonshine.Modular.QParam

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.TsumDivsorsAntidiagonal
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open scoped BigOperators
open scoped Real
open scoped NNReal
open scoped ENNReal

open Complex UpperHalfPlane EisensteinSeries

/-!
Kernel-pure q-expansion theorems for the normalized level-1 Eisenstein modular forms `E4`, `E6`.

Sprint items:
1. Prove `qExpansion₁ E4 = E4_q_expected` and `qExpansion₁ E6 = E6_q_expected`.
2. (Downstream file) use these to derive the Laurent expansion of `kleinJ₀`.
-/

/-!
## Zeta(6) in a kernel-pure way

Mathlib provides `riemannZeta_four`; we prove the corresponding `riemannZeta_six` lemma here.
-/

private lemma bernoulli_six : bernoulli 6 = (1 / 42 : ℚ) := by
  let f : ℕ → ℚ := fun k ↦ (Nat.choose 7 k : ℚ) * bernoulli k
  let S : ℕ → ℚ := fun n ↦ (Finset.range n).sum f
  have h : S 7 = (0 : ℚ) := by
    have hsum : S 7 = (if (7 : ℕ) = 1 then (1 : ℚ) else 0) := by
      dsimp [S, f]
      exact sum_bernoulli 7
    calc
      S 7 = (if (7 : ℕ) = 1 then (1 : ℚ) else 0) := hsum
      _ = 0 := by simp
  have hs : S 7 = S 6 + f 6 := by
    dsimp [S]
    exact Finset.sum_range_succ f 6
  have hf6 : f 6 = -S 6 := by
    linarith [h, hs]
  have hsum6 : S 6 = (-1 / 6 : ℚ) := by
    have hB5 : bernoulli' 5 = 0 :=
      bernoulli'_odd_eq_zero (by decide : Odd 5) (by decide : 1 < 5)
    have hc2 : (Nat.choose 7 2 : ℚ) = 21 := by
      exact_mod_cast (show Nat.choose 7 2 = 21 by native_decide)
    have hc4 : (Nat.choose 7 4 : ℚ) = 35 := by
      exact_mod_cast (show Nat.choose 7 4 = 35 by native_decide)
    simp [S, f, Finset.sum_range_succ, bernoulli_eq_bernoulli'_of_ne_one,
      bernoulli'_zero, bernoulli'_two, bernoulli'_three, bernoulli'_four, hB5, hc2, hc4]
    norm_num
  have h7 : (7 : ℚ) ≠ 0 := by norm_num
  have h' : (7 : ℚ) * bernoulli 6 = (1 / 6 : ℚ) := by
    have : f 6 = (1 / 6 : ℚ) := by
      nlinarith [hf6, hsum6]
    simpa [f] using this
  have : bernoulli 6 = (1 / 42 : ℚ) := by
    calc
      bernoulli 6 = (1 / 7 : ℚ) * ((7 : ℚ) * bernoulli 6) := by
        field_simp [h7]
      _ = (1 / 7 : ℚ) * (1 / 6 : ℚ) := by simp [h']
      _ = (1 / 42 : ℚ) := by norm_num
  simpa using this

private lemma riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have hb : (bernoulli 6 : ℂ) = (1 / 42 : ℂ) := by
    simpa using congrArg (fun x : ℚ => (x : ℂ)) bernoulli_six
  have h := riemannZeta_two_mul_nat (k := 3) (by decide : (3 : ℕ) ≠ 0)
  have h' : riemannZeta 6 =
      ((2 : ℂ) ^ 5) * (π : ℂ) ^ 6 * (bernoulli 6 : ℂ) / (Nat.factorial 6) := by
    have h6 : (2 : ℂ) * (3 : ℂ) = (6 : ℂ) := by norm_num
    have h5 : (2 * (3 : ℕ) - 1 : ℕ) = 5 := by decide
    simpa [h6, h5, Nat.factorial, div_eq_mul_inv, pow_succ, pow_add, mul_assoc, mul_left_comm,
      mul_comm] using h
  have hfac : ((2 : ℂ) ^ 5) * ((42 : ℂ)⁻¹) / (Nat.factorial 6) = ((945 : ℂ)⁻¹) := by
    norm_num [Nat.factorial, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    riemannZeta 6
        = ((2 : ℂ) ^ 5) * (π : ℂ) ^ 6 * (1 / 42 : ℂ) / (Nat.factorial 6) := by
          simpa [hb] using h'
    _ = (π : ℂ) ^ 6 * (((2 : ℂ) ^ 5) * (1 / 42 : ℂ) / (Nat.factorial 6)) := by ring
    _ = (π : ℂ) ^ 6 * ((945 : ℂ)⁻¹) := by
          have hfac1 :
              ((2 : ℂ) ^ 5) * (1 / 42 : ℂ) / (Nat.factorial 6) = ((945 : ℂ)⁻¹) := by
            simpa [one_div] using hfac
          rw [hfac1]
    _ = (π : ℂ) ^ 6 / 945 := by simp [div_eq_mul_inv]

/-!
## Full Eisenstein sum and its q-expansion

We first compute the classical q-expansion for the full (non-coprime) Eisenstein sum
`G_k(z) = ∑_{(c,d)∈ℤ²} (c z + d)^{-k}` for `k = 4, 6`.
-/

private def fullEis (k : ℤ) (z : ℍ) : ℂ :=
  ∑' x : (Fin 2 → ℤ), eisSummand k x z

private lemma fullEis_eq_tsum_int_tsum_int {k : ℤ} (hk : 3 ≤ k) (z : ℍ) :
    fullEis k z = ∑' c : ℤ, ∑' d : ℤ, (((c : ℂ) * (z : ℂ) + d) ^ (-k)) := by
  classical
  have hs : Summable (fun x : Fin 2 → ℤ ↦ eisSummand k x z) :=
    (summable_norm_eisSummand hk z).of_norm
  -- Reindex `Fin 2 → ℤ` as `ℤ × ℤ`, then apply Fubini.
  have hs' : Summable fun p : ℤ × ℤ ↦ eisSummand k ((finTwoArrowEquiv ℤ).symm p) z :=
    hs.comp_injective (finTwoArrowEquiv ℤ).symm.injective
  have hs_prod : Summable fun p : ℤ × ℤ ↦ (((p.1 : ℂ) * (z : ℂ) + p.2) ^ (-k)) := by
    simpa [eisSummand, finTwoArrowEquiv_symm_apply, Function.comp_def] using hs'
  calc
    fullEis k z
        = ∑' p : ℤ × ℤ, (((p.1 : ℂ) * (z : ℂ) + p.2) ^ (-k)) := by
            unfold fullEis
            -- `Equiv.tsum_eq` reindexes the summation along the equivalence.
            simpa [eisSummand, finTwoArrowEquiv_symm_apply, Function.comp_def, mul_assoc, add_assoc,
              add_left_comm, add_comm] using
              (Equiv.tsum_eq (finTwoArrowEquiv ℤ).symm
                (f := fun x : Fin 2 → ℤ => eisSummand k x z)).symm
    _ = ∑' c : ℤ, ∑' d : ℤ, (((c : ℂ) * (z : ℂ) + d) ^ (-k)) := by
          simpa using hs_prod.tsum_prod

private lemma tsum_int_div_pow_four (c : ℕ+) (z : ℍ) :
    (∑' d : ℤ, 1 / (((c : ℂ) * (z : ℂ) + d) ^ (4 : ℕ))) =
      ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
        ∑' n : ℕ+, (n : ℂ) ^ (3 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
  -- Apply the key identity at the point `c • z`.
  let zc : ℍ := ⟨(c : ℂ) * (z : ℂ), by
    have hc : (0 : ℝ) < (c : ℝ) := by exact_mod_cast c.pos
    simpa [mul_assoc] using (mul_pos hc z.2)⟩
  have h :=
    EisensteinSeries.qExpansion_identity_pnat (k := 3) (hk := by decide) (z := zc)
  -- Rewrite the exponential term as `q(z)^(c*n)`.
  have hq :
      Complex.exp (2 * π * Complex.I * (zc : ℂ)) = (q z) ^ (c : ℕ) := by
    -- `q z = exp (2π i z)` and `exp (2π i (c*z)) = (exp (2π i z))^c`.
    -- Use `exp_nsmul'` with `p = 1`.
    simpa [HeytingLean.Moonshine.Modular.q, Function.Periodic.qParam, zc, div_one, mul_assoc,
      mul_left_comm, mul_comm] using
      (Complex.exp_nsmul' (x := (z : ℂ)) (a := (2 * π * Complex.I)) (p := (1 : ℂ)) (n := (c : ℕ)))
  have hpow (n : ℕ+) :
      Complex.exp (2 * π * Complex.I * (zc : ℂ)) ^ (n : ℕ) = (q z) ^ ((c : ℕ) * (n : ℕ)) := by
    calc
      Complex.exp (2 * π * Complex.I * (zc : ℂ)) ^ (n : ℕ)
          = ((q z) ^ (c : ℕ)) ^ (n : ℕ) := by simp [hq]
      _ = (q z) ^ ((c : ℕ) * (n : ℕ)) := by simp [pow_mul]
  -- Finish by rewriting `zc` and simplifying constants.
  have h' :
      (∑' d : ℤ, 1 / (((c : ℂ) * (z : ℂ) + d) ^ (4 : ℕ))) =
        ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
          ∑' n : ℕ+, (n : ℂ) ^ (3 : ℕ) * (Complex.exp (2 * π * Complex.I * (zc : ℂ))) ^ (n : ℕ) := by
    -- This is just `h` with `zc` unfolded and cosmetic rewriting.
    simpa [zc, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  -- Push `hpow` through the `tsum`.
  simpa [hpow, h'] using h'

private lemma tsum_int_div_pow_six (c : ℕ+) (z : ℍ) :
    (∑' d : ℤ, 1 / (((c : ℂ) * (z : ℂ) + d) ^ (6 : ℕ))) =
      ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
        ∑' n : ℕ+, (n : ℂ) ^ (5 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
  let zc : ℍ := ⟨(c : ℂ) * (z : ℂ), by
    have hc : (0 : ℝ) < (c : ℝ) := by exact_mod_cast c.pos
    simpa [mul_assoc] using (mul_pos hc z.2)⟩
  have h :=
    EisensteinSeries.qExpansion_identity_pnat (k := 5) (hk := by decide) (z := zc)
  have hq :
      Complex.exp (2 * π * Complex.I * (zc : ℂ)) = (q z) ^ (c : ℕ) := by
    simpa [HeytingLean.Moonshine.Modular.q, Function.Periodic.qParam, zc, div_one, mul_assoc,
      mul_left_comm, mul_comm] using
      (Complex.exp_nsmul' (x := (z : ℂ)) (a := (2 * π * Complex.I)) (p := (1 : ℂ)) (n := (c : ℕ)))
  have hpow (n : ℕ+) :
      Complex.exp (2 * π * Complex.I * (zc : ℂ)) ^ (n : ℕ) = (q z) ^ ((c : ℕ) * (n : ℕ)) := by
    calc
      Complex.exp (2 * π * Complex.I * (zc : ℂ)) ^ (n : ℕ)
          = ((q z) ^ (c : ℕ)) ^ (n : ℕ) := by simp [hq]
      _ = (q z) ^ ((c : ℕ) * (n : ℕ)) := by simp [pow_mul]
  have h' :
      (∑' d : ℤ, 1 / (((c : ℂ) * (z : ℂ) + d) ^ (6 : ℕ))) =
        ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
          ∑' n : ℕ+, (n : ℂ) ^ (5 : ℕ) * (Complex.exp (2 * π * Complex.I * (zc : ℂ))) ^ (n : ℕ) := by
    simpa [zc, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  simpa [hpow, h'] using h'

private lemma fullEis_four_qexp (z : ℍ) :
    fullEis (4 : ℤ) z =
      (2 : ℂ) * riemannZeta 4 +
        (2 : ℂ) * ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ) := by
  classical
  -- Rewrite `fullEis` as an iterated sum over `c : ℤ`, then split into `c = 0` and `c ≠ 0`.
  have h4 : (3 : ℤ) ≤ (4 : ℤ) := by decide
  have hs := fullEis_eq_tsum_int_tsum_int (k := (4 : ℤ)) h4 z
  let f : ℤ → ℂ := fun c ↦ ∑' d : ℤ, 1 / (((c : ℂ) * (z : ℂ) + d) ^ (4 : ℕ))
  have hf_even : ∀ c : ℤ, f (-c) = f c := by
    intro c
    dsimp [f]
    -- Normalize `(((-c : ℤ) : ℂ)` to `-(c : ℂ)` so `Equiv.tsum_eq` matches the LHS.
    simp [Int.cast_neg]
    -- Reindex `d ↦ -d`, then simplify using `(-x)^4 = x^4`.
    -- `Equiv.tsum_eq` is `∑ d, g (-d) = ∑ d, g d`; we use it backwards.
    rw [← Equiv.tsum_eq (Equiv.neg ℤ)
      (f := fun d : ℤ => ((-((c : ℂ) * (z : ℂ)) + d) ^ (4 : ℕ))⁻¹)]
    refine tsum_congr (fun d => ?_)
    have hlin :
        (-(d : ℂ) + -((c : ℂ) * (z : ℂ))) = -(((c : ℂ) * (z : ℂ) + d) : ℂ) := by
      ring
    have hpow :
        (-(d : ℂ) + -((c : ℂ) * (z : ℂ))) ^ (4 : ℕ) =
          (((c : ℂ) * (z : ℂ) + d) : ℂ) ^ (4 : ℕ) := by
      -- Rewrite the base, then use `Even.neg_pow`.
      rw [hlin]
      simpa using (show (-(((c : ℂ) * (z : ℂ) + d) : ℂ)) ^ (4 : ℕ) =
          (((c : ℂ) * (z : ℂ) + d) : ℂ) ^ (4 : ℕ) from
        (show Even (4 : ℕ) by decide).neg_pow (((c : ℂ) * (z : ℂ) + d) : ℂ))
    simpa [add_comm] using hpow
  -- Summability of the outer `c`-sum follows from summability of `fullEis`.
  have hsum_f : Summable fun c : ℤ ↦ ∑' d : ℤ, (((c : ℂ) * (z : ℂ) + d) ^ (-(4 : ℤ))) := by
    -- This is `Summable.prod` applied to the summable function on `ℤ × ℤ`.
    have hs_prod : Summable fun p : ℤ × ℤ ↦ (((p.1 : ℂ) * (z : ℂ) + p.2) ^ (-(4 : ℤ))) := by
      -- From `summable_norm_eisSummand` via the proof above.
      have hs0 : Summable (fun x : Fin 2 → ℤ ↦ eisSummand (4 : ℤ) x z) :=
        (summable_norm_eisSummand (k := (4 : ℤ)) (by decide) z).of_norm
      have hs1 :
          Summable fun p : ℤ × ℤ ↦ eisSummand (4 : ℤ) ((finTwoArrowEquiv ℤ).symm p) z :=
        hs0.comp_injective (finTwoArrowEquiv ℤ).symm.injective
      simpa [eisSummand, finTwoArrowEquiv_symm_apply, Function.comp_def] using hs1
    simpa using hs_prod.prod
  -- Convert `x^(-4)` to `1 / x^4` pointwise, so we can apply `tsum_int_eq_zero_add_two_mul_tsum_pnat`.
  have hsum_f' : Summable f := by
    let f' : ℤ → ℂ := fun c ↦ ∑' d : ℤ, (((c : ℂ) * (z : ℂ) + d) ^ (-(4 : ℤ)))
    have hf' : f = f' := by
      funext c
      refine tsum_congr (fun d => ?_)
      simp [zpow_neg, div_eq_mul_inv]
      rfl
    -- `hsum_f` is summability of `f'`.
    simpa [hf'] using (hsum_f : Summable f')
  have hsplit :
      (∑' c : ℤ, f c) = f 0 + 2 * ∑' c : ℕ+, f c := by
    simpa using (tsum_int_eq_zero_add_two_mul_tsum_pnat (f := f) (hf := hf_even) (hf2 := hsum_f'))
  have hfull : fullEis (4 : ℤ) z = ∑' c : ℤ, f c := by
    -- Convert the `zpow` in `hs` to `1 / _^4`.
    -- `simp` sees `(- (4:ℤ))` is `-(4:ℕ)` after rewriting.
    have : ∑' c : ℤ, ∑' d : ℤ, (((c : ℂ) * (z : ℂ) + d) ^ (-(4 : ℤ))) = ∑' c : ℤ, f c := by
      refine tsum_congr (fun c => ?_)
      refine tsum_congr (fun d => ?_)
      simp [zpow_neg, div_eq_mul_inv]
      rfl
    exact hs.trans this
  have hf0 : f 0 = (2 : ℂ) * riemannZeta 4 := by
    have hz :
        (2 : ℂ) * riemannZeta 4 = ∑' n : ℤ, ((n : ℂ) ^ (4 : ℕ))⁻¹ := by
      simpa using
        (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 4) (by decide) (by decide))
    -- `f 0` is exactly this sum (`0 * z + d = d`).
    -- Rewrite RHS via `hz`, then simplify `f 0`.
    rw [hz]
    simp [f, one_div]
  have hq : ‖q z‖ < 1 := norm_q_lt_one z
  have hpos :
      (∑' c : ℕ+, f c) =
        ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ) := by
    -- Expand the `c`-sum using `tsum_int_div_pow_four`, then apply Lambert-series reindexing.
    have h1 :
        (∑' c : ℕ+, f c) =
          ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
            ∑' c : ℕ+, ∑' n : ℕ+, (n : ℂ) ^ (3 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
      -- First rewrite each `f c` using `tsum_int_div_pow_four`, then pull out the scalar.
      have hrewrite :
          (fun c : ℕ+ => f c) =
            fun c : ℕ+ =>
              ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
                ∑' n : ℕ+, (n : ℂ) ^ (3 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
        funext c
        simpa [f, mul_assoc, mul_left_comm, mul_comm] using (tsum_int_div_pow_four c z)
      calc
        (∑' c : ℕ+, f c)
            = ∑' c : ℕ+,
                ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
                  ∑' n : ℕ+, (n : ℂ) ^ (3 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
                    simp [hrewrite]
        _ = ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
              ∑' c : ℕ+, ∑' n : ℕ+, (n : ℂ) ^ (3 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
              simp [tsum_mul_left]
    have h2 :
        (∑' c : ℕ+, ∑' n : ℕ+, (n : ℂ) ^ (3 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ))) =
          ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ) := by
      -- `tsum_prod_pow_eq_tsum_sigma` matches after swapping multiplication order.
      simpa using (tsum_prod_pow_eq_tsum_sigma (𝕜 := ℂ) (k := 3) (r := q z) hq)
    simpa [h2, mul_assoc] using h1
  calc
    fullEis (4 : ℤ) z
        = ∑' c : ℤ, f c := hfull
    _ = f 0 + 2 * ∑' c : ℕ+, f c := by simp [hsplit]
    _ = (2 : ℂ) * riemannZeta 4 +
        (2 : ℂ) * ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ) := by
          simp [hf0, hpos, mul_assoc, mul_comm]

private lemma fullEis_six_qexp (z : ℍ) :
    fullEis (6 : ℤ) z =
      (2 : ℂ) * riemannZeta 6 +
        (2 : ℂ) * ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ) := by
  classical
  have h6 : (3 : ℤ) ≤ (6 : ℤ) := by decide
  have hs := fullEis_eq_tsum_int_tsum_int (k := (6 : ℤ)) h6 z
  let f : ℤ → ℂ := fun c ↦ ∑' d : ℤ, 1 / (((c : ℂ) * (z : ℂ) + d) ^ (6 : ℕ))
  have hf_even : ∀ c : ℤ, f (-c) = f c := by
    intro c
    dsimp [f]
    simp [Int.cast_neg]
    rw [← Equiv.tsum_eq (Equiv.neg ℤ)
      (f := fun d : ℤ => ((-((c : ℂ) * (z : ℂ)) + d) ^ (6 : ℕ))⁻¹)]
    refine tsum_congr (fun d => ?_)
    have hlin :
        (-(d : ℂ) + -((c : ℂ) * (z : ℂ))) = -(((c : ℂ) * (z : ℂ) + d) : ℂ) := by
      ring
    have hpow :
        (-(d : ℂ) + -((c : ℂ) * (z : ℂ))) ^ (6 : ℕ) =
          (((c : ℂ) * (z : ℂ) + d) : ℂ) ^ (6 : ℕ) := by
      rw [hlin]
      simpa using (show (-(((c : ℂ) * (z : ℂ) + d) : ℂ)) ^ (6 : ℕ) =
          (((c : ℂ) * (z : ℂ) + d) : ℂ) ^ (6 : ℕ) from
        (show Even (6 : ℕ) by decide).neg_pow (((c : ℂ) * (z : ℂ) + d) : ℂ))
    simpa [add_comm] using hpow
  -- Summability of the outer `c`-sum follows from summability of `fullEis`.
  have hsum_f : Summable fun c : ℤ ↦ ∑' d : ℤ, (((c : ℂ) * (z : ℂ) + d) ^ (-(6 : ℤ))) := by
    have hs_prod : Summable fun p : ℤ × ℤ ↦ (((p.1 : ℂ) * (z : ℂ) + p.2) ^ (-(6 : ℤ))) := by
      have hs0 : Summable (fun x : Fin 2 → ℤ ↦ eisSummand (6 : ℤ) x z) :=
        (summable_norm_eisSummand (k := (6 : ℤ)) (by decide) z).of_norm
      have hs1 :
          Summable fun p : ℤ × ℤ ↦ eisSummand (6 : ℤ) ((finTwoArrowEquiv ℤ).symm p) z :=
        hs0.comp_injective (finTwoArrowEquiv ℤ).symm.injective
      simpa [eisSummand, finTwoArrowEquiv_symm_apply, Function.comp_def] using hs1
    simpa using hs_prod.prod
  have hsum_f' : Summable f := by
    let f' : ℤ → ℂ := fun c ↦ ∑' d : ℤ, (((c : ℂ) * (z : ℂ) + d) ^ (-(6 : ℤ)))
    have hf' : f = f' := by
      funext c
      refine tsum_congr (fun d => ?_)
      simp [zpow_neg, div_eq_mul_inv]
      rfl
    simpa [hf'] using (hsum_f : Summable f')
  have hsplit :
      (∑' c : ℤ, f c) = f 0 + 2 * ∑' c : ℕ+, f c := by
    simpa using (tsum_int_eq_zero_add_two_mul_tsum_pnat (f := f) (hf := hf_even) (hf2 := hsum_f'))
  have hfull : fullEis (6 : ℤ) z = ∑' c : ℤ, f c := by
    have : ∑' c : ℤ, ∑' d : ℤ, (((c : ℂ) * (z : ℂ) + d) ^ (-(6 : ℤ))) = ∑' c : ℤ, f c := by
      refine tsum_congr (fun c => ?_)
      refine tsum_congr (fun d => ?_)
      simp [zpow_neg, div_eq_mul_inv]
      rfl
    exact hs.trans this
  have hf0 : f 0 = (2 : ℂ) * riemannZeta 6 := by
    have hz :
        (2 : ℂ) * riemannZeta 6 = ∑' n : ℤ, ((n : ℂ) ^ (6 : ℕ))⁻¹ := by
      simpa using
        (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 6) (by decide) (by decide))
    rw [hz]
    simp [f, one_div]
  have hq : ‖q z‖ < 1 := norm_q_lt_one z
  have hpos :
      (∑' c : ℕ+, f c) =
        ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ) := by
    have h1 :
        (∑' c : ℕ+, f c) =
          ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
            ∑' c : ℕ+, ∑' n : ℕ+, (n : ℂ) ^ (5 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
      have hrewrite :
          (fun c : ℕ+ => f c) =
            fun c : ℕ+ =>
              ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
                ∑' n : ℕ+, (n : ℂ) ^ (5 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
        funext c
        simpa [f, mul_assoc, mul_left_comm, mul_comm] using (tsum_int_div_pow_six c z)
      calc
        (∑' c : ℕ+, f c)
            = ∑' c : ℕ+,
                ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
                  ∑' n : ℕ+, (n : ℂ) ^ (5 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
                    simp [hrewrite]
        _ = ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
              ∑' c : ℕ+, ∑' n : ℕ+, (n : ℂ) ^ (5 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ)) := by
              simp [tsum_mul_left]
    have h2 :
        (∑' c : ℕ+, ∑' n : ℕ+, (n : ℂ) ^ (5 : ℕ) * (q z) ^ ((c : ℕ) * (n : ℕ))) =
          ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ) := by
      simpa using (tsum_prod_pow_eq_tsum_sigma (𝕜 := ℂ) (k := 5) (r := q z) hq)
    simpa [h2, mul_assoc] using h1
  calc
    fullEis (6 : ℤ) z
        = ∑' c : ℤ, f c := hfull
    _ = f 0 + 2 * ∑' c : ℕ+, f c := by simp [hsplit]
    _ = (2 : ℂ) * riemannZeta 6 +
        (2 : ℂ) * ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ) := by
          simp [hf0, hpos, mul_assoc, mul_comm]

/-!
## gcd decomposition

We decompose the full lattice sum by gcd and relate it to the coprime Eisenstein sum used by
`ModularForm.E`.
-/

private lemma fullEis_eq_tsum_sigma_gammaSet {k : ℤ} (hk : 3 ≤ k) (z : ℍ) :
    fullEis k z =
      ∑' r : ℕ, ∑' v : EisensteinSeries.gammaSet 1 r (0 : Fin 2 → ZMod 1), eisSummand k v z := by
  classical
  have hs : Summable (fun x : Fin 2 → ℤ ↦ eisSummand k x z) :=
    (summable_norm_eisSummand hk z).of_norm
  -- Reindex by `(Fin 2 → ℤ) ≃ Σ r, gammaSet 1 r 0`.
  have hsσ :
      Summable (fun p : (Σ r : ℕ, EisensteinSeries.gammaSet 1 r (0 : Fin 2 → ZMod 1)) ↦
        eisSummand k (EisensteinSeries.gammaSetDivGcdSigmaEquiv.symm p) z) :=
    hs.comp_injective EisensteinSeries.gammaSetDivGcdSigmaEquiv.symm.injective
  have hreindex :
      (∑' p : (Σ r : ℕ, EisensteinSeries.gammaSet 1 r (0 : Fin 2 → ZMod 1)),
          eisSummand k (EisensteinSeries.gammaSetDivGcdSigmaEquiv.symm p) z) =
        (∑' x : Fin 2 → ℤ, eisSummand k x z) := by
    simpa using
      (Equiv.tsum_eq EisensteinSeries.gammaSetDivGcdSigmaEquiv.symm
        (f := fun x : Fin 2 → ℤ => eisSummand k x z))
  have hiter :
      (∑' p : (Σ r : ℕ, EisensteinSeries.gammaSet 1 r (0 : Fin 2 → ZMod 1)),
          eisSummand k (EisensteinSeries.gammaSetDivGcdSigmaEquiv.symm p) z)
        =
        ∑' r : ℕ,
          ∑' v : EisensteinSeries.gammaSet 1 r (0 : Fin 2 → ZMod 1),
            eisSummand k (EisensteinSeries.gammaSetDivGcdSigmaEquiv.symm ⟨r, v⟩) z := by
    simpa using (hsσ.tsum_sigma)
  -- Simplify the `symm` form.
  have hsimp :
      (fun r : ℕ =>
          ∑' v : EisensteinSeries.gammaSet 1 r (0 : Fin 2 → ZMod 1),
            eisSummand k (EisensteinSeries.gammaSetDivGcdSigmaEquiv.symm ⟨r, v⟩) z)
        =
      (fun r : ℕ =>
          ∑' v : EisensteinSeries.gammaSet 1 r (0 : Fin 2 → ZMod 1), eisSummand k v z) := by
    funext r
    refine tsum_congr (fun v => ?_)
    simp [EisensteinSeries.gammaSetDivGcdSigmaEquiv_symm_eq]
  -- Assemble.
  unfold fullEis
  simpa [hreindex.symm, hiter, hsimp]

private def coprimeEis (k : ℤ) (z : ℍ) : ℂ :=
  ∑' v : EisensteinSeries.gammaSet 1 1 (0 : Fin 2 → ZMod 1), eisSummand k v z

private lemma coprimeEis_eq_eisensteinSeries (k : ℤ) (z : ℍ) :
    coprimeEis k z = eisensteinSeries (N := 1) (a := (0 : Fin 2 → ZMod 1)) k z := by
  rfl

private lemma eisSummand_smul (k : ℤ) (r : ℕ) (v : Fin 2 → ℤ) (z : ℍ) :
    eisSummand k (r • v) z =
      ((r : ℂ) ^ (-k)) * eisSummand k v z := by
  -- Work with the simplified `ℤ`-scalar-multiplication form and then factor out `r`.
  let A : ℂ := ((v 0 : ℂ) * (z : ℂ)) + (v 1 : ℂ)
  have hbase :
      ((r • v) 0 : ℂ) * (z : ℂ) + (r • v) 1 = (r : ℂ) * A := by
    simp [A, Pi.smul_apply, Int.cast_mul, Int.cast_natCast]
    ring
  have hcomm : Commute (r : ℂ) A := by
    simpa [Commute] using (mul_comm (r : ℂ) A)
  -- Keep the goal in `zpow` form (avoid rewriting `zpow` into inverses of `pow`).
  unfold eisSummand
  -- Rewrite the LHS into `(r * A) ^ (-k)`, then apply `Commute.mul_zpow`.
  rw [hbase]
  -- `eisSummand k v z` is `A ^ (-k)` by definition.
  simpa [A] using (hcomm.mul_zpow (-k))

private lemma fullEis_eq_riemannZeta_mul_coprimeEis (k : ℕ) (hk : 3 ≤ k) (z : ℍ) :
    fullEis (k : ℤ) z = riemannZeta k * coprimeEis (k : ℤ) z := by
  classical
  have hk0 : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hk)
  have hk' : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hσ := fullEis_eq_tsum_sigma_gammaSet (k := (k : ℤ)) hk' z
  let fiber : ℕ → ℂ := fun r =>
    ∑' v : EisensteinSeries.gammaSet 1 r (0 : Fin 2 → ZMod 1), eisSummand (k : ℤ) v z
  have hσ' : fullEis (k : ℤ) z = ∑' r : ℕ, fiber r := by
    simpa [fiber] using hσ
  have hfiber : ∀ r : ℕ, fiber r = ((r : ℂ) ^ (-(k : ℤ))) * coprimeEis (k : ℤ) z := by
    intro r
    cases r with
    | zero =>
        -- Only `v = 0` has `gcd = 0`, so the fiber sum is `0`; also `0^(-k) = 0`.
        have hsub : Subsingleton (EisensteinSeries.gammaSet 1 0 (0 : Fin 2 → ZMod 1)) := by
          refine ⟨?_⟩
          intro x y
          -- Any element of `gammaSet 1 0 0` is the zero vector.
          have hxg : (x.1 0).gcd (x.1 1) = 0 :=
            (EisensteinSeries.gammaSet_one_mem_iff (r := 0) (v := x.1)).1 x.2
          have hyg : (y.1 0).gcd (y.1 1) = 0 :=
            (EisensteinSeries.gammaSet_one_mem_iff (r := 0) (v := y.1)).1 y.2
          have hx0 : x.1 0 = 0 := (Int.gcd_eq_zero_iff.mp hxg).1
          have hx1 : x.1 1 = 0 := (Int.gcd_eq_zero_iff.mp hxg).2
          have hy0 : y.1 0 = 0 := (Int.gcd_eq_zero_iff.mp hyg).1
          have hy1 : y.1 1 = 0 := (Int.gcd_eq_zero_iff.mp hyg).2
          apply Subtype.ext
          ext i
          fin_cases i <;> simp [hx0, hx1, hy0, hy1]
        classical
        let a0 : EisensteinSeries.gammaSet 1 0 (0 : Fin 2 → ZMod 1) :=
          ⟨(0 : Fin 2 → ℤ), by
            -- Membership is just `gcd = 0` at level 1.
            exact (EisensteinSeries.gammaSet_one_mem_iff (r := 0) (v := (0 : Fin 2 → ℤ))).2 (by simp)⟩
        have hf0 : fiber 0 = eisSummand (k : ℤ) (a0 : Fin 2 → ℤ) z := by
          -- `gammaSet 1 0 0` is a singleton type, so the `tsum` collapses.
          have hzero :
              ∀ b : EisensteinSeries.gammaSet 1 0 (0 : Fin 2 → ZMod 1),
                b ≠ a0 → eisSummand (k : ℤ) (b : Fin 2 → ℤ) z = 0 := by
            intro b hb
            exfalso
            exact hb (Subsingleton.elim b a0)
          simpa [fiber, a0] using (tsum_eq_single a0 hzero)
        -- Now evaluate the (single) term and simplify the scalar `0^(-k)`.
        have hsummand0 : eisSummand (k : ℤ) (a0 : Fin 2 → ℤ) z = 0 := by
          simp [a0, eisSummand, hk0]
        simp [hf0, hsummand0, coprimeEis, hk0]
    | succ r =>
        haveI : NeZero (Nat.succ r) := ⟨Nat.succ_ne_zero _⟩
        let e :
            EisensteinSeries.gammaSet 1 (Nat.succ r) (0 : Fin 2 → ZMod 1) ≃
              EisensteinSeries.gammaSet 1 1 (0 : Fin 2 → ZMod 1) :=
          EisensteinSeries.gammaSetDivGcdEquiv (r := Nat.succ r)
        -- Reindex the sum along the equivalence.
        have hre :
            fiber (Nat.succ r) =
              ∑' w : EisensteinSeries.gammaSet 1 1 (0 : Fin 2 → ZMod 1), eisSummand (k : ℤ) (e.symm w) z := by
          -- `Equiv.tsum_eq e.symm` gives `∑ w, f (e.symm w) = ∑ v, f v`.
          simpa [fiber] using
            (Equiv.tsum_eq (e := e.symm) (f := fun v : EisensteinSeries.gammaSet 1 (Nat.succ r)
              (0 : Fin 2 → ZMod 1) => eisSummand (k : ℤ) v z)).symm
        -- Pointwise, `e.symm w` is `(Nat.succ r) • w` on the underlying vector.
        have hterm (w : EisensteinSeries.gammaSet 1 1 (0 : Fin 2 → ZMod 1)) :
            eisSummand (k : ℤ) (e.symm w) z =
              ((Nat.succ r : ℂ) ^ (-(k : ℤ))) * eisSummand (k : ℤ) w z := by
          set v : EisensteinSeries.gammaSet 1 (Nat.succ r) (0 : Fin 2 → ZMod 1) := e.symm w
          have hv :
              (v : Fin 2 → ℤ) = (Nat.succ r) • EisensteinSeries.divIntMap (Nat.succ r) (v : Fin 2 → ℤ) :=
            EisensteinSeries.gammaSet_eq_gcd_mul_divIntMap (r := Nat.succ r) (v := (v : Fin 2 → ℤ)) v.2
          have hdiv :
              EisensteinSeries.divIntMap (Nat.succ r) (v : Fin 2 → ℤ) = (w : Fin 2 → ℤ) := by
            -- `e v = w`, and `e v` is `divIntMap` on the underlying vector.
            have hevw : e v = w := by simp [v]
            simpa [EisensteinSeries.gammaSetDivGcdEquiv_eq] using (congrArg Subtype.val hevw)
          have hvw : (v : Fin 2 → ℤ) = (Nat.succ r) • (w : Fin 2 → ℤ) := by
            calc
              (v : Fin 2 → ℤ)
                  = (Nat.succ r) • EisensteinSeries.divIntMap (Nat.succ r) (v : Fin 2 → ℤ) := hv
              _ = (Nat.succ r) • (w : Fin 2 → ℤ) := by
                    simpa using congrArg (fun t : Fin 2 → ℤ => (Nat.succ r) • t) hdiv
          -- Rewrite using `hvw` and apply `eisSummand_smul`.
          simpa [v, hvw] using (eisSummand_smul (k := (k : ℤ)) (r := Nat.succ r) (v := (w : Fin 2 → ℤ)) z)
        -- Finish the fiber computation.
        calc
          fiber (Nat.succ r)
              = ∑' w : EisensteinSeries.gammaSet 1 1 (0 : Fin 2 → ZMod 1), eisSummand (k : ℤ) (e.symm w) z := hre
          _ = ∑' w : EisensteinSeries.gammaSet 1 1 (0 : Fin 2 → ZMod 1),
                ((Nat.succ r : ℂ) ^ (-(k : ℤ))) * eisSummand (k : ℤ) w z := by
                refine tsum_congr (fun w => ?_)
                simpa using (hterm w)
          _ = ((Nat.succ r : ℂ) ^ (-(k : ℤ))) * coprimeEis (k : ℤ) z := by
                simp [coprimeEis, tsum_mul_left]
  -- Substitute the fiberwise formula into the outer sum and factor out the constant.
  have hfull : fullEis (k : ℤ) z = (∑' r : ℕ, (r : ℂ) ^ (-(k : ℤ))) * coprimeEis (k : ℤ) z := by
    calc
      fullEis (k : ℤ) z = ∑' r : ℕ, fiber r := hσ'
      _ = ∑' r : ℕ, ((r : ℂ) ^ (-(k : ℤ))) * coprimeEis (k : ℤ) z := by
            refine tsum_congr (fun r => ?_)
            simp [hfiber r]
      _ = (∑' r : ℕ, (r : ℂ) ^ (-(k : ℤ))) * coprimeEis (k : ℤ) z := by
            simp [tsum_mul_right]
  have hk1 : (1 : ℕ) < k := lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hk
  have hzeta : riemannZeta k = ∑' n : ℕ, 1 / (n : ℂ) ^ k := zeta_nat_eq_tsum_of_gt_one hk1
  have hzeta' : (∑' n : ℕ, (n : ℂ) ^ (-(k : ℤ))) = riemannZeta k := by
    have : (fun n : ℕ => 1 / (n : ℂ) ^ k) = fun n : ℕ => (n : ℂ) ^ (-(k : ℤ)) := by
      funext n
      simp [one_div, zpow_neg]
    simpa [this] using hzeta.symm
  -- Conclude.
  calc
    fullEis (k : ℤ) z
        = (∑' r : ℕ, (r : ℂ) ^ (-(k : ℤ))) * coprimeEis (k : ℤ) z := hfull
    _ = riemannZeta k * coprimeEis (k : ℤ) z := by
      -- Rewrite the sum as `ζ(k)` (avoid `simp` cancelling the right factor).
      rw [hzeta']

/-!
## The normalized Eisenstein modular forms `E4`, `E6`

We now turn the full-lattice q-expansions into explicit q-expansions for the normalized modular
forms `E4`, `E6`.
-/

private lemma riemannZeta_four_ne_zero : (riemannZeta 4 : ℂ) ≠ 0 := by
  -- `ζ(4) = π^4 / 90`.
  have hπ : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [riemannZeta_four]
  exact div_ne_zero (pow_ne_zero 4 hπ) (by norm_num : (90 : ℂ) ≠ 0)

private lemma riemannZeta_six_ne_zero : (riemannZeta 6 : ℂ) ≠ 0 := by
  have hπ : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [riemannZeta_six]
  exact div_ne_zero (pow_ne_zero 6 hπ) (by norm_num : (945 : ℂ) ≠ 0)

private lemma E4_eq_half_mul_eisensteinSeries (z : ℍ) :
    E4 z = (1 / 2 : ℂ) * eisensteinSeries (N := 1) (a := (0 : Fin 2 → ZMod 1)) (4 : ℤ) z := by
  -- Unfold `E4 = ModularForm.E` and reduce `eisensteinSeries_MF` pointwise.
  unfold HeytingLean.Moonshine.Modular.E4
  -- `simp` reduces the scalar action and the `eisensteinSeries_MF` record fields.
  simp [ModularForm.E, ModularForm.eisensteinSeries_MF, smul_eq_mul]
  -- The remaining coercion is exactly `eisensteinSeries_SIF_apply`.
  simpa using (EisensteinSeries.eisensteinSeries_SIF_apply (N := 1) (a := (0 : Fin 2 → ZMod 1))
    (k := (4 : ℤ)) z)

private lemma E6_eq_half_mul_eisensteinSeries (z : ℍ) :
    E6 z = (1 / 2 : ℂ) * eisensteinSeries (N := 1) (a := (0 : Fin 2 → ZMod 1)) (6 : ℤ) z := by
  unfold HeytingLean.Moonshine.Modular.E6
  simp [ModularForm.E, ModularForm.eisensteinSeries_MF, smul_eq_mul]
  simpa using (EisensteinSeries.eisensteinSeries_SIF_apply (N := 1) (a := (0 : Fin 2 → ZMod 1))
    (k := (6 : ℤ)) z)

private lemma E4_qexp_pointwise (z : ℍ) :
    E4 z =
      (1 : ℂ) +
        (240 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ) := by
  -- Move from `E4` to the coprime Eisenstein sum.
  have hE4 : E4 z = (1 / 2 : ℂ) * coprimeEis (4 : ℤ) z := by
    simpa [coprimeEis_eq_eisensteinSeries] using (E4_eq_half_mul_eisensteinSeries (z := z))
  have hfull :
      fullEis (4 : ℤ) z = riemannZeta 4 * coprimeEis (4 : ℤ) z :=
    (fullEis_eq_riemannZeta_mul_coprimeEis (k := 4) (hk := by decide) z)
  have hq := fullEis_four_qexp z
  -- Solve for `coprimeEis` by multiplying the identity by `ζ(4)⁻¹`.
  have hcop :
      coprimeEis (4 : ℤ) z =
        (2 : ℂ) +
          (480 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ) := by
    have hq' :
        riemannZeta 4 * coprimeEis (4 : ℤ) z =
          (2 : ℂ) * riemannZeta 4 +
            (2 : ℂ) * ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
              ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ) := by
      simpa [hfull] using hq
    have hz : (riemannZeta 4 : ℂ) ≠ 0 := riemannZeta_four_ne_zero
    have hq'' := congrArg (fun t => (riemannZeta 4)⁻¹ * t) hq'
    -- Simplify both sides and compute the constant `(((-2πi)^4 / 3!) / ζ(4)) = 240`.
    have hconst :
        ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) / (riemannZeta 4) = (240 : ℂ) := by
      -- `(-2πi)^4 = 16 * π^4` and `ζ(4) = π^4 / 90`.
      rw [riemannZeta_four]
      have hπ : (π : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      field_simp [hz, hπ]
      ring_nf
      norm_num [Nat.factorial]
    -- Finish `hcop`.
    have hl :
        (riemannZeta 4)⁻¹ * (riemannZeta 4 * coprimeEis (4 : ℤ) z) = coprimeEis (4 : ℤ) z := by
      simp [hz]
    have hr :
        (riemannZeta 4)⁻¹ *
            ((2 : ℂ) * riemannZeta 4 +
              (2 : ℂ) * ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3)) *
                ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ))
          =
          (2 : ℂ) +
            (480 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ) := by
      set S : ℂ := ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ)
      set C4 : ℂ := ((-2 * π * Complex.I) ^ (4 : ℕ) / (Nat.factorial 3))
      have h1 : (riemannZeta 4)⁻¹ * ((2 : ℂ) * riemannZeta 4) = (2 : ℂ) := by
        calc
          (riemannZeta 4)⁻¹ * ((2 : ℂ) * riemannZeta 4)
              = (2 : ℂ) * ((riemannZeta 4)⁻¹ * riemannZeta 4) := by ring
          _ = (2 : ℂ) := by simp [hz]
      have h2 : (riemannZeta 4)⁻¹ * ((2 : ℂ) * C4 * S) = (480 : ℂ) * S := by
        have hnum : (2 : ℂ) * (C4 / riemannZeta 4) = (480 : ℂ) := by
          -- `C4 / ζ(4) = 240`.
          simp [hconst]
          norm_num
        calc
          (riemannZeta 4)⁻¹ * ((2 : ℂ) * C4 * S)
              = ((2 : ℂ) * (C4 / riemannZeta 4)) * S := by
                  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          _ = (480 : ℂ) * S := by
                  simp [hnum]
      -- Reassemble (do not unfold `S`/`C4` before using `h1`/`h2`).
      have :
          (riemannZeta 4)⁻¹ * ((2 : ℂ) * riemannZeta 4 + (2 : ℂ) * C4 * S) =
            (2 : ℂ) + (480 : ℂ) * S := by
        have h2' : (riemannZeta 4)⁻¹ * ((2 : ℂ) * (C4 * S)) = (480 : ℂ) * S := by
          simpa [mul_assoc] using h2
        calc
          (riemannZeta 4)⁻¹ * ((2 : ℂ) * riemannZeta 4 + (2 : ℂ) * C4 * S)
              = (riemannZeta 4)⁻¹ * ((2 : ℂ) * riemannZeta 4) +
                  (riemannZeta 4)⁻¹ * ((2 : ℂ) * C4 * S) := by
                    ring
          _ = (2 : ℂ) + (480 : ℂ) * S := by
                -- `ring` may regroup as `2 * (C4 * S)`, so use `h2'`.
                simp [h1, h2', mul_assoc]
      simpa [S, C4, mul_assoc] using this
    exact (hl ▸ (hq''.trans hr))
  -- Scale by `1/2`.
  calc
    E4 z = (1 / 2 : ℂ) * coprimeEis (4 : ℤ) z := hE4
    _ =
        (1 : ℂ) +
          (240 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ) := by
          -- `1/2 * 2 = 1` and `1/2 * 480 = 240`.
          set S : ℂ := ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * (q z) ^ (e : ℕ)
          have hcop' : coprimeEis (4 : ℤ) z = (2 : ℂ) + (480 : ℂ) * S := by
            simpa [S] using hcop
          have hscale := congrArg (fun t => (1 / 2 : ℂ) * t) hcop'
          -- Now simplify the RHS numerically.
          -- (We rewrite `E4 z` using `hE4` and then rewrite using `hscale`.)
          -- `ring_nf` turns `1/2 * 480` into `240`.
          have hrhs :
              (1 / 2 : ℂ) * ((2 : ℂ) + (480 : ℂ) * S) = (1 : ℂ) + (240 : ℂ) * S := by
            ring_nf
          -- Finish.
          -- `hscale` gives `(1/2) * coprimeEis = (1/2) * (2 + 480*S)`.
          -- The goal at this point is about `(1/2) * coprimeEis`, not `E4`.
          simpa [S] using hscale.trans hrhs

private lemma E6_qexp_pointwise (z : ℍ) :
    E6 z =
      (1 : ℂ) +
        (-504 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ) := by
  have hE6 : E6 z = (1 / 2 : ℂ) * coprimeEis (6 : ℤ) z := by
    simpa [coprimeEis_eq_eisensteinSeries] using (E6_eq_half_mul_eisensteinSeries (z := z))
  have hfull :
      fullEis (6 : ℤ) z = riemannZeta 6 * coprimeEis (6 : ℤ) z :=
    (fullEis_eq_riemannZeta_mul_coprimeEis (k := 6) (hk := by decide) z)
  have hq := fullEis_six_qexp z
  have hcop :
      coprimeEis (6 : ℤ) z =
        (2 : ℂ) +
          (-1008 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ) := by
    have hq' :
        riemannZeta 6 * coprimeEis (6 : ℤ) z =
          (2 : ℂ) * riemannZeta 6 +
            (2 : ℂ) * ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
              ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ) := by
      simpa [hfull] using hq
    have hz : (riemannZeta 6 : ℂ) ≠ 0 := riemannZeta_six_ne_zero
    have hq'' := congrArg (fun t => (riemannZeta 6)⁻¹ * t) hq'
    have hconst :
        ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) / (riemannZeta 6) = (-504 : ℂ) := by
      rw [riemannZeta_six]
      have hπ : (π : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      field_simp [hz, hπ]
      ring_nf
      have hI : (Complex.I : ℂ) ^ (6 : ℕ) = (-1 : ℂ) := by
        -- Reduce modulo 4: `I^6 = I^(6 % 4) = I^2 = -1`.
        have hmod : (Complex.I : ℂ) ^ (6 : ℕ) = (Complex.I : ℂ) ^ (6 % 4) :=
          Complex.I_pow_eq_pow_mod (n := 6)
        -- `simp` evaluates `6 % 4` and `I^2`.
        simpa using (hmod.trans (by simp))
      -- After clearing denominators, this is a pure numeric identity.
      simp [hI, Nat.factorial]
      norm_num
    have hl :
        (riemannZeta 6)⁻¹ * (riemannZeta 6 * coprimeEis (6 : ℤ) z) = coprimeEis (6 : ℤ) z := by
      simp [hz]
    have hr :
        (riemannZeta 6)⁻¹ *
            ((2 : ℂ) * riemannZeta 6 +
              (2 : ℂ) * ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5)) *
                ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ))
          =
          (2 : ℂ) +
            (-1008 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ) := by
      set S : ℂ := ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ)
      set C6 : ℂ := ((-2 * π * Complex.I) ^ (6 : ℕ) / (Nat.factorial 5))
      have h1 : (riemannZeta 6)⁻¹ * ((2 : ℂ) * riemannZeta 6) = (2 : ℂ) := by
        calc
          (riemannZeta 6)⁻¹ * ((2 : ℂ) * riemannZeta 6)
              = (2 : ℂ) * ((riemannZeta 6)⁻¹ * riemannZeta 6) := by ring
          _ = (2 : ℂ) := by simp [hz]
      have h2 : (riemannZeta 6)⁻¹ * ((2 : ℂ) * C6 * S) = (-1008 : ℂ) * S := by
        have hnum : (2 : ℂ) * (C6 / riemannZeta 6) = (-1008 : ℂ) := by
          simp [hconst]
          norm_num
        calc
          (riemannZeta 6)⁻¹ * ((2 : ℂ) * C6 * S)
              = ((2 : ℂ) * (C6 / riemannZeta 6)) * S := by
                  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          _ = (-1008 : ℂ) * S := by
                  simp [hnum]
      have :
          (riemannZeta 6)⁻¹ * ((2 : ℂ) * riemannZeta 6 + (2 : ℂ) * C6 * S) =
            (2 : ℂ) + (-1008 : ℂ) * S := by
        have h2' : (riemannZeta 6)⁻¹ * ((2 : ℂ) * (C6 * S)) = (-1008 : ℂ) * S := by
          simpa [mul_assoc] using h2
        calc
          (riemannZeta 6)⁻¹ * ((2 : ℂ) * riemannZeta 6 + (2 : ℂ) * C6 * S)
              = (riemannZeta 6)⁻¹ * ((2 : ℂ) * riemannZeta 6) +
                  (riemannZeta 6)⁻¹ * ((2 : ℂ) * C6 * S) := by
                    ring
          _ = (2 : ℂ) + (-1008 : ℂ) * S := by
                simp [h1, h2', mul_assoc]
      simpa [S, C6, mul_assoc] using this
    exact (hl ▸ (hq''.trans hr))
  calc
    E6 z = (1 / 2 : ℂ) * coprimeEis (6 : ℤ) z := hE6
    _ =
        (1 : ℂ) +
          (-504 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ) := by
          set S : ℂ := ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * (q z) ^ (e : ℕ)
          have hcop' : coprimeEis (6 : ℤ) z = (2 : ℂ) + (-1008 : ℂ) * S := by
            simpa [S] using hcop
          have hscale := congrArg (fun t => (1 / 2 : ℂ) * t) hcop'
          have hrhs :
              (1 / 2 : ℂ) * ((2 : ℂ) + (-1008 : ℂ) * S) = (1 : ℂ) + (-504 : ℂ) * S := by
            ring_nf
          simpa [S] using hscale.trans hrhs

/-!
## Identifying `qExpansion₁` with the classical coefficient formulas

We compare the `q`-expansion defined by `ModularFormClass.qExpansion` (the Taylor series of the
cusp function) with the explicit coefficient power series `E4_q_expected`, `E6_q_expected`.
-/

open scoped Topology

open Filter

private abbrev E4_expected_coeff : ℕ → ℂ := fun n => E4_q_expected.coeff n
private abbrev E6_expected_coeff : ℕ → ℂ := fun n => E6_q_expected.coeff n

private abbrev E4_expected_fms : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) E4_expected_coeff

private abbrev E6_expected_fms : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) E6_expected_coeff

private abbrev E4_expected_fun : ℂ → ℂ :=
  E4_expected_fms.sum

private abbrev E6_expected_fun : ℂ → ℂ :=
  E6_expected_fms.sum

private lemma sigma_le_pow_succ (k : ℕ) (n : ℕ) :
    ArithmeticFunction.sigma k n ≤ n ^ (k + 1) := by
  -- `σ_k(n) = ∑_{d|n} d^k ≤ (#divisors n) * n^k ≤ n * n^k = n^(k+1)`.
  classical
  have hsum :
      ArithmeticFunction.sigma k n ≤ n.divisors.card * (n ^ k) := by
    -- Termwise bound `d^k ≤ n^k`.
    rw [ArithmeticFunction.sigma_apply]
    -- Bound by a sum of constant `n^k`.
    have : (∑ d ∈ n.divisors, d ^ k) ≤ ∑ _d ∈ n.divisors, n ^ k := by
      refine Finset.sum_le_sum ?_
      intro d hd
      have hdn : d ≤ n := Nat.divisor_le hd
      exact pow_le_pow_left' hdn k
    -- Evaluate the RHS sum.
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hcard : n.divisors.card ≤ n := Nat.card_divisors_le_self n
  -- Combine.
  calc
    ArithmeticFunction.sigma k n ≤ n.divisors.card * (n ^ k) := hsum
    _ ≤ n * (n ^ k) := Nat.mul_le_mul_right _ hcard
    _ = n ^ (k + 1) := by simp [pow_succ, Nat.mul_comm]

set_option maxHeartbeats 800000 in
private lemma E4_expected_radius_pos : 0 < E4_expected_fms.radius := by
  -- Show `1/2 ≤ radius`, hence the radius is positive.
  let r : ℝ≥0 := (1 / 2 : ℝ≥0)
  have hr : ‖(r : ℝ)‖ < 1 := by norm_num
  have hgeom : Summable fun n : ℕ => ((r : ℝ) ^ n) := by
    simpa using (summable_geometric_of_norm_lt_one (x := (r : ℝ)) hr)
  have hpoly : Summable fun n : ℕ => ((n : ℝ) ^ 4) * ((r : ℝ) ^ n) := by
    simpa [Real.norm_eq_abs] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (k := 4) (r := (r : ℝ)) hr)
  have hpoly' : Summable fun n : ℕ => (240 : ℝ) * (((n : ℝ) ^ 4) * ((r : ℝ) ^ n)) :=
    hpoly.mul_left (240 : ℝ)
  have hs_g :
      Summable fun n : ℕ => ((r : ℝ) ^ n) + (240 : ℝ) * (((n : ℝ) ^ 4) * ((r : ℝ) ^ n)) :=
    hgeom.add hpoly'
  have hle :
      ∀ n : ℕ,
        ‖E4_expected_fms n‖ * ((r : ℝ) ^ n) ≤
          ((r : ℝ) ^ n) + (240 : ℝ) * (((n : ℝ) ^ 4) * ((r : ℝ) ^ n)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [E4_expected_fms, E4_expected_coeff]
    · -- `n > 0`: use `σ₃(n) ≤ n^4`.
      have hsigma : (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ) ^ 4 := by
        have hs' : ArithmeticFunction.sigma 3 n ≤ n ^ (3 + 1) := sigma_le_pow_succ 3 n
        -- `3+1 = 4`.
        simpa using (show (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ) ^ 4 from by
          exact_mod_cast hs')
      have hcoeff :
          ‖E4_expected_fms n‖ ≤ (240 : ℝ) * ((n : ℝ) ^ 4) := by
        -- Unfold the scalar coefficient and take norms.
        have hcn : (E4_expected_coeff n) = (240 : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) := by
          simpa [E4_expected_coeff] using (E4_q_expected_coeff_of_ne_zero (n := n) hn)
        -- `‖ofScalars‖ = ‖coeff‖` (NormOneClass).
        have hn_fms : ‖E4_expected_fms n‖ = ‖E4_expected_coeff n‖ := by
          simp [E4_expected_fms]
        -- Now bound the coefficient norm by `240 * n^4`.
        have : ‖E4_expected_coeff n‖ ≤ (240 : ℝ) * (ArithmeticFunction.sigma 3 n : ℝ) := by
          -- `‖240 * σ‖ = ‖240‖ * ‖σ‖` and both are `Nat`s.
          simp [E4_expected_coeff, hcn]
        calc
          ‖E4_expected_fms n‖ = ‖E4_expected_coeff n‖ := hn_fms
          _ ≤ (240 : ℝ) * (ArithmeticFunction.sigma 3 n : ℝ) := this
          _ ≤ (240 : ℝ) * ((n : ℝ) ^ 4) := by gcongr
      have hmul :
          ‖E4_expected_fms n‖ * ((r : ℝ) ^ n) ≤
            (240 : ℝ) * (((n : ℝ) ^ 4) * ((r : ℝ) ^ n)) := by
        calc
          ‖E4_expected_fms n‖ * ((r : ℝ) ^ n)
              ≤ ((240 : ℝ) * ((n : ℝ) ^ 4)) * ((r : ℝ) ^ n) := by
                    gcongr
          _ = (240 : ℝ) * (((n : ℝ) ^ 4) * ((r : ℝ) ^ n)) := by ring
      -- Add a nonnegative geometric term.
      have : (240 : ℝ) * (((n : ℝ) ^ 4) * ((r : ℝ) ^ n)) ≤
          ((r : ℝ) ^ n) + (240 : ℝ) * (((n : ℝ) ^ 4) * ((r : ℝ) ^ n)) :=
        le_add_of_nonneg_left (by positivity)
      exact hmul.trans this
  have hs :
      Summable fun n : ℕ => ‖E4_expected_fms n‖ * ((r : ℝ) ^ n) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => ((r : ℝ) ^ n) + (240 : ℝ) * (((n : ℝ) ^ 4) * ((r : ℝ) ^ n)))
      (g := fun n : ℕ => ‖E4_expected_fms n‖ * ((r : ℝ) ^ n))
      (fun _ => by positivity) (fun n => hle n) hs_g
  have hrle : (r : ℝ≥0∞) ≤ E4_expected_fms.radius :=
    E4_expected_fms.le_radius_of_summable_norm (r := r) (by simpa using hs)
  exact lt_of_lt_of_le (by
    -- `0 < (r : ℝ≥0∞)`.
    simpa using (show (0 : ℝ≥0∞) < (r : ℝ≥0∞) from by
      exact_mod_cast (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)))) hrle

set_option maxHeartbeats 800000 in
private lemma E6_expected_radius_pos : 0 < E6_expected_fms.radius := by
  -- Same argument as for `E4`, with `σ₅(n) ≤ n^6` and constant `504`.
  let r : ℝ≥0 := (1 / 2 : ℝ≥0)
  have hr : ‖(r : ℝ)‖ < 1 := by norm_num
  have hgeom : Summable fun n : ℕ => ((r : ℝ) ^ n) := by
    simpa using (summable_geometric_of_norm_lt_one (x := (r : ℝ)) hr)
  have hpoly : Summable fun n : ℕ => ((n : ℝ) ^ 6) * ((r : ℝ) ^ n) := by
    simpa [Real.norm_eq_abs] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (k := 6) (r := (r : ℝ)) hr)
  have hpoly' : Summable fun n : ℕ => (504 : ℝ) * (((n : ℝ) ^ 6) * ((r : ℝ) ^ n)) :=
    hpoly.mul_left (504 : ℝ)
  have hs_g :
      Summable fun n : ℕ => ((r : ℝ) ^ n) + (504 : ℝ) * (((n : ℝ) ^ 6) * ((r : ℝ) ^ n)) :=
    hgeom.add hpoly'
  have hle :
      ∀ n : ℕ,
        ‖E6_expected_fms n‖ * ((r : ℝ) ^ n) ≤
          ((r : ℝ) ^ n) + (504 : ℝ) * (((n : ℝ) ^ 6) * ((r : ℝ) ^ n)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [E6_expected_fms, E6_expected_coeff]
    · have hsigma : (ArithmeticFunction.sigma 5 n : ℝ) ≤ (n : ℝ) ^ 6 := by
        have hs' : ArithmeticFunction.sigma 5 n ≤ n ^ (5 + 1) := sigma_le_pow_succ 5 n
        simpa using (show (ArithmeticFunction.sigma 5 n : ℝ) ≤ (n : ℝ) ^ 6 from by
          exact_mod_cast hs')
      have hcoeff :
          ‖E6_expected_fms n‖ ≤ (504 : ℝ) * ((n : ℝ) ^ 6) := by
        have hcn : (E6_expected_coeff n) = (-504 : ℂ) * (ArithmeticFunction.sigma 5 n : ℂ) := by
          simpa [E6_expected_coeff] using (E6_q_expected_coeff_of_ne_zero (n := n) hn)
        have hn_fms : ‖E6_expected_fms n‖ = ‖E6_expected_coeff n‖ := by
          simp [E6_expected_fms]
        have : ‖E6_expected_coeff n‖ ≤ (504 : ℝ) * (ArithmeticFunction.sigma 5 n : ℝ) := by
          -- `‖-504‖ = 504`.
          simp [E6_expected_coeff, hcn]
        calc
          ‖E6_expected_fms n‖ = ‖E6_expected_coeff n‖ := hn_fms
          _ ≤ (504 : ℝ) * (ArithmeticFunction.sigma 5 n : ℝ) := this
          _ ≤ (504 : ℝ) * ((n : ℝ) ^ 6) := by gcongr
      have hmul :
          ‖E6_expected_fms n‖ * ((r : ℝ) ^ n) ≤
            (504 : ℝ) * (((n : ℝ) ^ 6) * ((r : ℝ) ^ n)) := by
        calc
          ‖E6_expected_fms n‖ * ((r : ℝ) ^ n)
              ≤ ((504 : ℝ) * ((n : ℝ) ^ 6)) * ((r : ℝ) ^ n) := by
                    gcongr
          _ = (504 : ℝ) * (((n : ℝ) ^ 6) * ((r : ℝ) ^ n)) := by ring
      have : (504 : ℝ) * (((n : ℝ) ^ 6) * ((r : ℝ) ^ n)) ≤
          ((r : ℝ) ^ n) + (504 : ℝ) * (((n : ℝ) ^ 6) * ((r : ℝ) ^ n)) :=
        le_add_of_nonneg_left (by positivity)
      exact hmul.trans this
  have hs :
      Summable fun n : ℕ => ‖E6_expected_fms n‖ * ((r : ℝ) ^ n) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => ((r : ℝ) ^ n) + (504 : ℝ) * (((n : ℝ) ^ 6) * ((r : ℝ) ^ n)))
      (g := fun n : ℕ => ‖E6_expected_fms n‖ * ((r : ℝ) ^ n))
      (fun _ => by positivity) (fun n => hle n) hs_g
  have hrle : (r : ℝ≥0∞) ≤ E6_expected_fms.radius :=
    E6_expected_fms.le_radius_of_summable_norm (r := r) (by simpa using hs)
  exact lt_of_lt_of_le (by
    simpa using (show (0 : ℝ≥0∞) < (r : ℝ≥0∞) from by
      exact_mod_cast (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)))) hrle

/-!
## Identifying `qExpansion₁` for `E4`/`E6`

We show that the `q`-expansion defined by `ModularFormClass.qExpansion` agrees with the classical
coefficient formulas packaged as `E4_q_expected`, `E6_q_expected`.
-/

open Filter

private lemma summable_E4_expected_coeff_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => E4_expected_coeff n * q ^ n) := by
  -- Absolute convergence via comparison with a polynomial times a geometric series.
  have hq' : ‖(‖q‖ : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)] using hq
  have hgeom : Summable fun n : ℕ => (‖q‖ : ℝ) ^ n := by
    simpa using (summable_geometric_of_norm_lt_one (x := (‖q‖ : ℝ)) hq')
  have hpoly : Summable fun n : ℕ => ((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n := by
    simpa [Real.norm_eq_abs] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (k := 4) (r := (‖q‖ : ℝ)) hq')
  have hpoly' :
      Summable fun n : ℕ => (240 : ℝ) * (((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n) :=
    hpoly.mul_left (240 : ℝ)
  have hsum :
      Summable fun n : ℕ => (‖q‖ : ℝ) ^ n + (240 : ℝ) * (((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n) :=
    hgeom.add hpoly'
  -- Compare norms termwise.
  refine Summable.of_norm_bounded hsum ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [E4_expected_coeff]
  · have hsigma : (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ) ^ 4 := by
      have hs' : ArithmeticFunction.sigma 3 n ≤ n ^ (3 + 1) := sigma_le_pow_succ 3 n
      simpa using (show (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ) ^ 4 from by
        exact_mod_cast hs')
    have hcoeff :
        ‖E4_expected_coeff n‖ ≤ (240 : ℝ) * ((n : ℝ) ^ 4) := by
      have hcn : E4_expected_coeff n = (240 : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) := by
        simpa [E4_expected_coeff] using (E4_q_expected_coeff_of_ne_zero (n := n) hn)
      have : ‖E4_expected_coeff n‖ ≤ (240 : ℝ) * (ArithmeticFunction.sigma 3 n : ℝ) := by
        simp [E4_expected_coeff, hcn]
      calc
        ‖E4_expected_coeff n‖ ≤ (240 : ℝ) * (ArithmeticFunction.sigma 3 n : ℝ) := this
        _ ≤ (240 : ℝ) * ((n : ℝ) ^ 4) := by gcongr
    calc
      ‖E4_expected_coeff n * q ^ n‖ = ‖E4_expected_coeff n‖ * ‖q ^ n‖ := by
        simp
      _ = ‖E4_expected_coeff n‖ * (‖q‖ : ℝ) ^ n := by simp [norm_pow]
      _ ≤ (240 : ℝ) * (((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n) := by
        have : ‖E4_expected_coeff n‖ * (‖q‖ : ℝ) ^ n ≤
            ((240 : ℝ) * ((n : ℝ) ^ 4)) * (‖q‖ : ℝ) ^ n := by
          gcongr
        -- rearrange
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      _ ≤ (‖q‖ : ℝ) ^ n + (240 : ℝ) * (((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n) := by
        exact le_add_of_nonneg_left (by positivity)

private lemma summable_E6_expected_coeff_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => E6_expected_coeff n * q ^ n) := by
  have hq' : ‖(‖q‖ : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)] using hq
  have hgeom : Summable fun n : ℕ => (‖q‖ : ℝ) ^ n := by
    simpa using (summable_geometric_of_norm_lt_one (x := (‖q‖ : ℝ)) hq')
  have hpoly : Summable fun n : ℕ => ((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n := by
    simpa [Real.norm_eq_abs] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (k := 6) (r := (‖q‖ : ℝ)) hq')
  have hpoly' :
      Summable fun n : ℕ => (504 : ℝ) * (((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n) :=
    hpoly.mul_left (504 : ℝ)
  have hsum :
      Summable fun n : ℕ => (‖q‖ : ℝ) ^ n + (504 : ℝ) * (((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n) :=
    hgeom.add hpoly'
  refine Summable.of_norm_bounded hsum ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [E6_expected_coeff]
  · have hsigma : (ArithmeticFunction.sigma 5 n : ℝ) ≤ (n : ℝ) ^ 6 := by
      have hs' : ArithmeticFunction.sigma 5 n ≤ n ^ (5 + 1) := sigma_le_pow_succ 5 n
      simpa using (show (ArithmeticFunction.sigma 5 n : ℝ) ≤ (n : ℝ) ^ 6 from by
        exact_mod_cast hs')
    have hcoeff :
        ‖E6_expected_coeff n‖ ≤ (504 : ℝ) * ((n : ℝ) ^ 6) := by
      have hcn : E6_expected_coeff n = (-504 : ℂ) * (ArithmeticFunction.sigma 5 n : ℂ) := by
        simpa [E6_expected_coeff] using (E6_q_expected_coeff_of_ne_zero (n := n) hn)
      have : ‖E6_expected_coeff n‖ ≤ (504 : ℝ) * (ArithmeticFunction.sigma 5 n : ℝ) := by
        simp [E6_expected_coeff, hcn]
      calc
        ‖E6_expected_coeff n‖ ≤ (504 : ℝ) * (ArithmeticFunction.sigma 5 n : ℝ) := this
        _ ≤ (504 : ℝ) * ((n : ℝ) ^ 6) := by gcongr
    calc
      ‖E6_expected_coeff n * q ^ n‖ = ‖E6_expected_coeff n‖ * ‖q ^ n‖ := by
        simp
      _ = ‖E6_expected_coeff n‖ * (‖q‖ : ℝ) ^ n := by simp [norm_pow]
      _ ≤ (504 : ℝ) * (((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n) := by
        have : ‖E6_expected_coeff n‖ * (‖q‖ : ℝ) ^ n ≤
            ((504 : ℝ) * ((n : ℝ) ^ 6)) * (‖q‖ : ℝ) ^ n := by
          gcongr
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      _ ≤ (‖q‖ : ℝ) ^ n + (504 : ℝ) * (((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n) := by
        exact le_add_of_nonneg_left (by positivity)

private lemma E4_expected_fun_eq_one_add (q : ℂ) (hq : ‖q‖ < 1) :
    E4_expected_fun q =
      (1 : ℂ) +
        (240 : ℂ) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * q ^ (e : ℕ) := by
  have hf : Summable (fun n : ℕ => E4_expected_coeff n * q ^ n) :=
    summable_E4_expected_coeff_mul_pow q hq
  -- Rewrite `E4_expected_fun` as a `tsum`.
  have htsum : E4_expected_fun q = ∑' n : ℕ, E4_expected_coeff n * q ^ n := by
    -- `E4_expected_fun` is the sum of an `ofScalars` formal power series.
    simpa [E4_expected_fun, E4_expected_fms, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
      (FormalMultilinearSeries.ofScalars_sum_eq (E := ℂ) (c := E4_expected_coeff) q)
  -- Split off the `n = 0` term.
  have hsplit :
      (E4_expected_coeff 0 * q ^ (0 : ℕ)) +
          ∑' e : ℕ+, E4_expected_coeff (e : ℕ) * q ^ (e : ℕ) =
        ∑' n : ℕ, E4_expected_coeff n * q ^ n := by
    simpa using (tsum_zero_pnat_eq_tsum_nat (f := fun n : ℕ => E4_expected_coeff n * q ^ n) hf)
  -- Evaluate the coefficients.
  have h0 : E4_expected_coeff 0 * q ^ (0 : ℕ) = (1 : ℂ) := by
    simp [E4_expected_coeff]
  have hpos :
      (∑' e : ℕ+, E4_expected_coeff (e : ℕ) * q ^ (e : ℕ)) =
          (240 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * q ^ (e : ℕ) := by
    -- Use the nonzero coefficient formula for all `e : ℕ+`.
    have hcoeff : ∀ e : ℕ+, E4_expected_coeff (e : ℕ) =
        (240 : ℂ) * (ArithmeticFunction.sigma 3 e : ℂ) := by
      intro e
      have he : (e : ℕ) ≠ 0 := Nat.ne_of_gt e.pos
      simpa [E4_expected_coeff] using (E4_q_expected_coeff_of_ne_zero (n := (e : ℕ)) he)
    -- Rewrite the summand, then factor out the constant using `tsum_mul_left`.
    calc
      (∑' e : ℕ+, E4_expected_coeff (e : ℕ) * q ^ (e : ℕ)) =
          ∑' e : ℕ+, (240 : ℂ) * ((ArithmeticFunction.sigma 3 e : ℂ) * q ^ (e : ℕ)) := by
            refine tsum_congr ?_
            intro e
            -- `((240 * σ) * q^e) = 240 * (σ * q^e)`
            simp [hcoeff, mul_assoc]
      _ = (240 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * q ^ (e : ℕ) := by
            simpa using
              (tsum_mul_left (a := (240 : ℂ))
                (f := fun e : ℕ+ => (ArithmeticFunction.sigma 3 e : ℂ) * q ^ (e : ℕ)))
  -- Assemble.
  have :
      (∑' n : ℕ, E4_expected_coeff n * q ^ n) =
        (1 : ℂ) + (240 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * q ^ (e : ℕ) := by
    rw [← hsplit, h0, hpos]
    -- The goal is now definitional.
  simpa [htsum] using this

private lemma E6_expected_fun_eq_one_add (q : ℂ) (hq : ‖q‖ < 1) :
    E6_expected_fun q =
      (1 : ℂ) +
        (-504 : ℂ) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * q ^ (e : ℕ) := by
  have hf : Summable (fun n : ℕ => E6_expected_coeff n * q ^ n) :=
    summable_E6_expected_coeff_mul_pow q hq
  have htsum : E6_expected_fun q = ∑' n : ℕ, E6_expected_coeff n * q ^ n := by
    simpa [E6_expected_fun, E6_expected_fms, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
      (FormalMultilinearSeries.ofScalars_sum_eq (E := ℂ) (c := E6_expected_coeff) q)
  have hsplit :
      (E6_expected_coeff 0 * q ^ (0 : ℕ)) +
          ∑' e : ℕ+, E6_expected_coeff (e : ℕ) * q ^ (e : ℕ) =
        ∑' n : ℕ, E6_expected_coeff n * q ^ n := by
    simpa using (tsum_zero_pnat_eq_tsum_nat (f := fun n : ℕ => E6_expected_coeff n * q ^ n) hf)
  have h0 : E6_expected_coeff 0 * q ^ (0 : ℕ) = (1 : ℂ) := by
    simp [E6_expected_coeff]
  have hpos :
      (∑' e : ℕ+, E6_expected_coeff (e : ℕ) * q ^ (e : ℕ)) =
          (-504 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * q ^ (e : ℕ) := by
    have hcoeff : ∀ e : ℕ+, E6_expected_coeff (e : ℕ) =
        (-504 : ℂ) * (ArithmeticFunction.sigma 5 e : ℂ) := by
      intro e
      have he : (e : ℕ) ≠ 0 := Nat.ne_of_gt e.pos
      simpa [E6_expected_coeff] using (E6_q_expected_coeff_of_ne_zero (n := (e : ℕ)) he)
    calc
      (∑' e : ℕ+, E6_expected_coeff (e : ℕ) * q ^ (e : ℕ)) =
          ∑' e : ℕ+, (-504 : ℂ) * ((ArithmeticFunction.sigma 5 e : ℂ) * q ^ (e : ℕ)) := by
            refine tsum_congr ?_
            intro e
            simp [hcoeff, mul_assoc]
      _ = (-504 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * q ^ (e : ℕ) := by
            simpa using
              (tsum_mul_left (a := (-504 : ℂ))
                (f := fun e : ℕ+ => (ArithmeticFunction.sigma 5 e : ℂ) * q ^ (e : ℕ)))
  have :
      (∑' n : ℕ, E6_expected_coeff n * q ^ n) =
        (1 : ℂ) + (-504 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * q ^ (e : ℕ) := by
    rw [← hsplit, h0, hpos]
  simpa [htsum] using this

private lemma E4_cusp_eq_one_add (w : ℂ) (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    E4_cusp w =
      (1 : ℂ) +
        (240 : ℂ) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * w ^ (e : ℕ) := by
  -- Choose `τ ∈ ℍ` with `qParam 1 τ = w`.
  let τc : ℂ := Function.Periodic.invQParam (h := (1 : ℝ)) w
  have hIm : 0 < τc.im :=
    Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := (1 : ℝ)) (hh := by norm_num) hw hw0
  let τ : ℍ := ⟨τc, hIm⟩
  have hwparam : Function.Periodic.qParam (h := (1 : ℝ)) τc = w :=
    Function.Periodic.qParam_right_inv (h := (1 : ℝ)) (by norm_num) hw0
  have hwparam' : Function.Periodic.qParam 1 τ = w := by
    simpa [τ, τc] using hwparam
  have hcusp : E4_cusp w = E4 τ := by
    simpa [hwparam'] using (E4_eq_E4_cusp (τ := τ))
  have hE4 : E4 τ =
      (1 : ℂ) +
        (240 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 3 e : ℂ) * w ^ (e : ℕ) := by
    -- Start from the pointwise identity and rewrite `q τ` as `w`.
    have h := E4_qexp_pointwise τ
    -- `q τ = qParam 1 τ = w`.
    simpa [q, hwparam', pow_mul] using h
  simpa [hcusp] using hE4

private lemma E6_cusp_eq_one_add (w : ℂ) (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    E6_cusp w =
      (1 : ℂ) +
        (-504 : ℂ) *
          ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * w ^ (e : ℕ) := by
  let τc : ℂ := Function.Periodic.invQParam (h := (1 : ℝ)) w
  have hIm : 0 < τc.im :=
    Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := (1 : ℝ)) (hh := by norm_num) hw hw0
  let τ : ℍ := ⟨τc, hIm⟩
  have hwparam : Function.Periodic.qParam (h := (1 : ℝ)) τc = w :=
    Function.Periodic.qParam_right_inv (h := (1 : ℝ)) (by norm_num) hw0
  have hwparam' : Function.Periodic.qParam 1 τ = w := by
    simpa [τ, τc] using hwparam
  have hcusp : E6_cusp w = E6 τ := by
    simpa [hwparam'] using (E6_eq_E6_cusp (τ := τ))
  have hE6 : E6 τ =
      (1 : ℂ) +
        (-504 : ℂ) * ∑' e : ℕ+, (ArithmeticFunction.sigma 5 e : ℂ) * w ^ (e : ℕ) := by
    have h := E6_qexp_pointwise τ
    simpa [q, hwparam', pow_mul] using h
  simpa [hcusp] using hE6

private lemma E4_cusp_eq_expected_fun_eventually :
    ∀ᶠ w in 𝓝 (0 : ℂ), E4_cusp w = E4_expected_fun w := by
  -- First show they agree on a punctured neighborhood.
  have heq_ne : ∀ᶠ w in 𝓝[({0} : Set ℂ)ᶜ] (0 : ℂ), E4_cusp w = E4_expected_fun w := by
    -- Use the set `ball 0 (1/2) ∩ {0}ᶜ`.
    have hmem :
        Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∩ ({0} : Set ℂ)ᶜ ∈ 𝓝[({0} : Set ℂ)ᶜ] (0 : ℂ) := by
      refine (mem_nhdsWithin_iff_exists_mem_nhds_inter).2 ?_
      refine ⟨Metric.ball (0 : ℂ) (1 / 2 : ℝ), Metric.ball_mem_nhds (0 : ℂ) (by norm_num), ?_⟩
      intro _w hw
      exact hw
    refine Filter.eventually_of_mem hmem ?_
    intro w hw
    have hw_ball : ‖w‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw.1
    have hw0 : w ≠ 0 := by
      simpa using hw.2
    have hw1 : ‖w‖ < 1 := lt_trans hw_ball (by norm_num)
    have hcusp := E4_cusp_eq_one_add w hw1 hw0
    have hexp := E4_expected_fun_eq_one_add w hw1
    simp [hcusp, hexp]
  -- Use analyticity (hence continuity) to show equality at `0`, then upgrade to `𝓝 0`.
  have hps_cusp :
      HasFPowerSeriesAt E4_cusp (ModularFormClass.qExpansionFormalMultilinearSeries 1 E4) 0 := by
    exact (ModularFormClass.hasFPowerSeries_cuspFunction (n := 1) (f := E4) |>.hasFPowerSeriesAt)
  have hps_exp :
      HasFPowerSeriesAt E4_expected_fun E4_expected_fms 0 := by
    simpa [E4_expected_fun] using
      (E4_expected_fms.hasFPowerSeriesOnBall E4_expected_radius_pos).hasFPowerSeriesAt
  have h0 : E4_cusp 0 = E4_expected_fun 0 := by
    have ht_cusp : Tendsto E4_cusp (𝓝[({0} : Set ℂ)ᶜ] (0 : ℂ)) (𝓝 (E4_cusp 0)) :=
      (hps_cusp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have ht_exp : Tendsto E4_expected_fun (𝓝[({0} : Set ℂ)ᶜ] (0 : ℂ)) (𝓝 (E4_expected_fun 0)) :=
      (hps_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    exact tendsto_nhds_unique_of_eventuallyEq ht_cusp ht_exp heq_ne
  -- Now show equality on `ball 0 (1/2)`, which is a neighborhood of `0`.
  have hball : Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds (0 : ℂ) (by norm_num)
  refine Filter.eventually_of_mem hball ?_
  intro w hw
  have hw_ball : ‖w‖ < (1 / 2 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hw1 : ‖w‖ < 1 := lt_trans hw_ball (by norm_num)
  by_cases hw0 : w = 0
  · subst hw0
    simp [h0]
  · have hcusp := E4_cusp_eq_one_add w hw1 hw0
    have hexp := E4_expected_fun_eq_one_add w hw1
    simp [hcusp, hexp]

  -- Note: the analogous `nhds`-equality lemma for `E6` is proved just below.
  private lemma E6_cusp_eq_expected_fun_eventually :
      ∀ᶠ w in 𝓝 (0 : ℂ), E6_cusp w = E6_expected_fun w := by
    have heq_ne : ∀ᶠ w in 𝓝[({0} : Set ℂ)ᶜ] (0 : ℂ), E6_cusp w = E6_expected_fun w := by
      have hmem :
          Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∩ ({0} : Set ℂ)ᶜ ∈ 𝓝[({0} : Set ℂ)ᶜ] (0 : ℂ) := by
        refine (mem_nhdsWithin_iff_exists_mem_nhds_inter).2 ?_
        refine ⟨Metric.ball (0 : ℂ) (1 / 2 : ℝ), Metric.ball_mem_nhds (0 : ℂ) (by norm_num), ?_⟩
        intro _w hw
        exact hw
      refine Filter.eventually_of_mem hmem ?_
      intro w hw
      have hw_ball : ‖w‖ < (1 / 2 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw.1
      have hw0 : w ≠ 0 := by
        simpa using hw.2
      have hw1 : ‖w‖ < 1 := lt_trans hw_ball (by norm_num)
      have hcusp := E6_cusp_eq_one_add w hw1 hw0
      have hexp := E6_expected_fun_eq_one_add w hw1
      simp [hcusp, hexp]
    have hps_cusp :
        HasFPowerSeriesAt E6_cusp (ModularFormClass.qExpansionFormalMultilinearSeries 1 E6) 0 := by
      exact (ModularFormClass.hasFPowerSeries_cuspFunction (n := 1) (f := E6) |>.hasFPowerSeriesAt)
    have hps_exp :
        HasFPowerSeriesAt E6_expected_fun E6_expected_fms 0 := by
      simpa [E6_expected_fun] using
        (E6_expected_fms.hasFPowerSeriesOnBall E6_expected_radius_pos).hasFPowerSeriesAt
    have h0 : E6_cusp 0 = E6_expected_fun 0 := by
      have ht_cusp : Tendsto E6_cusp (𝓝[({0} : Set ℂ)ᶜ] (0 : ℂ)) (𝓝 (E6_cusp 0)) :=
        (hps_cusp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      have ht_exp : Tendsto E6_expected_fun (𝓝[({0} : Set ℂ)ᶜ] (0 : ℂ)) (𝓝 (E6_expected_fun 0)) :=
        (hps_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      exact tendsto_nhds_unique_of_eventuallyEq ht_cusp ht_exp heq_ne
    have hball : Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds (0 : ℂ) (by norm_num)
    refine Filter.eventually_of_mem hball ?_
    intro w hw
    have hw_ball : ‖w‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hw1 : ‖w‖ < 1 := lt_trans hw_ball (by norm_num)
    by_cases hw0 : w = 0
    · subst hw0
      simp [h0]
    · have hcusp := E6_cusp_eq_one_add w hw1 hw0
      have hexp := E6_expected_fun_eq_one_add w hw1
      simp [hcusp, hexp]

theorem qExpansion₁_E4_eq_expected : qExpansion₁ E4 = E4_q_expected := by
  -- Compare `FormalMultilinearSeries` on the cusp function and use injectivity of `ofScalars`.
  have hps_cusp :
      HasFPowerSeriesAt E4_cusp (ModularFormClass.qExpansionFormalMultilinearSeries 1 E4) 0 := by
    have h :=
      (ModularFormClass.hasFPowerSeries_cuspFunction (n := 1) (f := E4) : _)
    exact h.hasFPowerSeriesAt
  have hps_exp :
      HasFPowerSeriesAt E4_expected_fun E4_expected_fms 0 := by
    have h :=
      (E4_expected_fms.hasFPowerSeriesOnBall E4_expected_radius_pos).hasFPowerSeriesAt
    simpa [E4_expected_fun] using h
  have hseries :
      ModularFormClass.qExpansionFormalMultilinearSeries 1 E4 = E4_expected_fms :=
    HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hps_cusp hps_exp
      E4_cusp_eq_expected_fun_eventually
  -- Turn this into coefficient equality, then `PowerSeries.ext`.
  classical
  ext n
  -- Rewrite both sides as `ofScalars` and use injectivity on coefficients.
  have :
      (fun m : ℕ => (qExpansion₁ E4).coeff m) = E4_expected_coeff := by
    -- `qExpansionFormalMultilinearSeries` and `E4_expected_fms` are both `ofScalars` series.
    have hleft :
        ModularFormClass.qExpansionFormalMultilinearSeries 1 E4 =
          FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) (fun m : ℕ => (qExpansion₁ E4).coeff m) := by
      ext m
      simp [ModularFormClass.qExpansionFormalMultilinearSeries, FormalMultilinearSeries.ofScalars, qExpansion₁]
    have hright :
        E4_expected_fms =
          FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) E4_expected_coeff := by
      rfl
    have hof :
        FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) (fun m : ℕ => (qExpansion₁ E4).coeff m) =
          FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) E4_expected_coeff := by
      simpa [hleft, hright] using hseries
    exact (FormalMultilinearSeries.ofScalars_series_eq_iff (𝕜 := ℂ) (E := ℂ)
      (c := fun m : ℕ => (qExpansion₁ E4).coeff m) E4_expected_coeff).1 hof
  simpa [E4_expected_coeff] using congrArg (fun c : ℕ → ℂ => c n) this

theorem qExpansion₁_E6_eq_expected : qExpansion₁ E6 = E6_q_expected := by
  have hps_cusp :
      HasFPowerSeriesAt E6_cusp (ModularFormClass.qExpansionFormalMultilinearSeries 1 E6) 0 := by
    have h :=
      (ModularFormClass.hasFPowerSeries_cuspFunction (n := 1) (f := E6) : _)
    exact h.hasFPowerSeriesAt
  have hps_exp :
      HasFPowerSeriesAt E6_expected_fun E6_expected_fms 0 := by
    have h :=
      (E6_expected_fms.hasFPowerSeriesOnBall E6_expected_radius_pos).hasFPowerSeriesAt
    simpa [E6_expected_fun] using h
  have hseries :
      ModularFormClass.qExpansionFormalMultilinearSeries 1 E6 = E6_expected_fms :=
    HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hps_cusp hps_exp
      E6_cusp_eq_expected_fun_eventually
  classical
  ext n
  have :
      (fun m : ℕ => (qExpansion₁ E6).coeff m) = E6_expected_coeff := by
    have hleft :
        ModularFormClass.qExpansionFormalMultilinearSeries 1 E6 =
          FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) (fun m : ℕ => (qExpansion₁ E6).coeff m) := by
      ext m
      simp [ModularFormClass.qExpansionFormalMultilinearSeries, FormalMultilinearSeries.ofScalars, qExpansion₁]
    have hright :
        E6_expected_fms =
          FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) E6_expected_coeff := by
      rfl
    have hof :
        FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) (fun m : ℕ => (qExpansion₁ E6).coeff m) =
          FormalMultilinearSeries.ofScalars (𝕜 := ℂ) (E := ℂ) E6_expected_coeff := by
      simpa [hleft, hright] using hseries
    exact (FormalMultilinearSeries.ofScalars_series_eq_iff (𝕜 := ℂ) (E := ℂ)
      (c := fun m : ℕ => (qExpansion₁ E6).coeff m) E6_expected_coeff).1 hof
  simpa [E6_expected_coeff] using congrArg (fun c : ℕ → ℂ => c n) this


end HeytingLean.Moonshine.Modular
