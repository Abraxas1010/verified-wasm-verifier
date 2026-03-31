import HeytingLean.Moonshine.Modular.KleinBfunExtTruncation
import HeytingLean.Moonshine.Modular.KleinDenominatorTailReduction

import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane
open scoped BigOperators

open scoped MatrixGroups

/-!
## Tail Majorant Route for `kleinB_tail_eval`

This module isolates the remaining quantitative obligation in the fd-tail route:
it suffices to bound a nonnegative coefficient series.
-/

lemma summable_psTerm_kleinBps_of_norm_lt_one_of_ne_zero
    (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    Summable (fun n : ℕ => psTerm kleinBps q n) := by
  let fD : ℕ → ℂ := fun n => psTerm kleinDps q n
  have hsD : Summable fD := by
    simpa [fD] using (summable_psTerm_kleinDps (q := q) hq)
  have hsDsucc : Summable (fun n : ℕ => fD (n + 1)) :=
    hsD.comp_injective (add_left_injective 1)
  have hcongr : ∀ n : ℕ, q⁻¹ * fD (n + 1) = psTerm kleinBps q n := by
    intro n
    have hmul :
        psTerm kleinBps q n * q = fD (n + 1) := by
      simpa [kleinBps, kleinDps, fD] using
        (psTerm_kleinBSeries_mul_q
          (E4ps := qExpansion₁ E4) (E6ps := qExpansion₁ E6) (q := q) (n := n))
    calc
      q⁻¹ * fD (n + 1) = q⁻¹ * (psTerm kleinBps q n * q) := by rw [hmul.symm]
      _ = psTerm kleinBps q n := by field_simp [hq0]
  exact (hsDsucc.mul_left q⁻¹).congr hcongr

lemma norm_q_pow_four_mul_kleinB_tail_eval_le_tsum_shift
    (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ‖q ^ 4 * kleinB_tail_eval q‖
      ≤ ∑' n : ℕ, ‖psTerm kleinBps q (n + 4)‖ := by
  let f : ℕ → ℂ := fun n => psTerm kleinBps q (n + 4)
  have hsB : Summable (fun n : ℕ => psTerm kleinBps q n) :=
    summable_psTerm_kleinBps_of_norm_lt_one_of_ne_zero (q := q) hq hq0
  have hsShift : Summable f := by
    simpa [f] using hsB.comp_injective (add_left_injective 4)
  let g : ℕ → ℂ := fun n => kleinBps.coeff (n + 4) * q ^ n
  have hsG : Summable g := by
    have hq4 : (q ^ 4 : ℂ) ≠ 0 := pow_ne_zero 4 hq0
    have hcongr : ∀ n : ℕ, (q ^ 4)⁻¹ * f n = g n := by
      intro n
      calc
        (q ^ 4)⁻¹ * f n = (q ^ 4)⁻¹ * (kleinBps.coeff (n + 4) * q ^ (n + 4)) := by
          simp [f, psTerm]
        _ = (q ^ 4)⁻¹ * (q ^ 4 * (kleinBps.coeff (n + 4) * q ^ n)) := by
          ring_nf
        _ = g n := by
          simp [g, hq4]
    exact (hsShift.mul_left ((q ^ 4)⁻¹)).congr hcongr
  have hseries :
      q ^ 4 * kleinB_tail_eval q = ∑' n : ℕ, f n := by
    calc
      q ^ 4 * kleinB_tail_eval q = q ^ 4 * (∑' n : ℕ, g n) := by
        simp [kleinB_tail_eval, g]
      _ = ∑' n : ℕ, q ^ 4 * g n := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using (hsG.tsum_mul_left (q ^ 4)).symm
      _ = ∑' n : ℕ, f n := by
        refine tsum_congr ?_
        intro n
        calc
          q ^ 4 * g n = q ^ 4 * (kleinBps.coeff (n + 4) * q ^ n) := by simp [g]
          _ = kleinBps.coeff (n + 4) * q ^ (n + 4) := by ring_nf
          _ = f n := by simp [f, psTerm]
  calc
    ‖q ^ 4 * kleinB_tail_eval q‖ = ‖∑' n : ℕ, f n‖ := by rw [hseries]
    _ ≤ ∑' n : ℕ, ‖f n‖ := by exact norm_tsum_le_tsum_norm hsShift.norm

lemma norm_q_pow_four_mul_kleinB_tail_eval_le_tsum_coeff
    (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ‖q ^ 4 * kleinB_tail_eval q‖
      ≤ ∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ‖q‖ ^ (n + 4) := by
  have hle :=
    norm_q_pow_four_mul_kleinB_tail_eval_le_tsum_shift (q := q) hq hq0
  have hcongr :
      (∑' n : ℕ, ‖psTerm kleinBps q (n + 4)‖) =
        ∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ‖q‖ ^ (n + 4) := by
    refine tsum_congr ?_
    intro n
    simp [psTerm, norm_pow]
  exact hle.trans_eq hcongr

theorem kleinDenom_ne_zero_global_of_fd_coeff_majorant_lt_1200
    (hCoeffFd : ∀ τ : ℍ, τ ∈ ModularGroup.fd →
      (∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ‖q τ‖ ^ (n + 4)) < (1200 : ℝ)) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  refine kleinDenom_ne_zero_global_of_fd_tail_lt_1200 ?_
  intro τ hτ
  have hle :
      ‖(q τ) ^ 4 * kleinB_tail_eval (q τ)‖
        ≤ ∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ‖q τ‖ ^ (n + 4) :=
    norm_q_pow_four_mul_kleinB_tail_eval_le_tsum_coeff
      (q := q τ) (hq := norm_q_lt_one τ) (hq0 := q_ne_zero τ)
  exact lt_of_le_of_lt hle (hCoeffFd τ hτ)

theorem kleinDenom_ne_zero_global_of_coeff_majorant_one_div_hundred_lt_1200
    (hSummable100 :
      Summable (fun n : ℕ => ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4))))
    (hBound100 :
      (∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4))) < (1200 : ℝ)) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  refine kleinDenom_ne_zero_global_of_fd_coeff_majorant_lt_1200 ?_
  intro τ hτ
  have hq : ‖q τ‖ ≤ (1 / 100 : ℝ) :=
    norm_q_le_one_div_hundred_of_mem_fd (τ := τ) hτ
  have hsB :
      Summable (fun n : ℕ => psTerm kleinBps (q τ) n) :=
    summable_psTerm_kleinBps_of_norm_lt_one_of_ne_zero
      (q := q τ) (hq := norm_q_lt_one τ) (hq0 := q_ne_zero τ)
  have hsShift :
      Summable (fun n : ℕ => psTerm kleinBps (q τ) (n + 4)) := by
    simpa using hsB.comp_injective (add_left_injective 4)
  have hsCoeffTau :
      Summable (fun n : ℕ => ‖kleinBps.coeff (n + 4)‖ * ‖q τ‖ ^ (n + 4)) := by
    refine hsShift.norm.congr ?_
    intro n
    simp [psTerm, norm_pow]
  have hterm :
      ∀ n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ‖q τ‖ ^ (n + 4)
        ≤ ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4)) := by
    intro n
    gcongr
  have hsum_le :
      (∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ‖q τ‖ ^ (n + 4))
        ≤ ∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4)) :=
    hsCoeffTau.tsum_le_tsum hterm hSummable100
  exact lt_of_le_of_lt hsum_le hBound100

lemma summable_coeff_majorant_one_div_hundred :
    Summable (fun n : ℕ => ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4))) := by
  let q0 : ℂ := (1 / 100 : ℂ)
  have hq : ‖q0‖ < 1 := by
    norm_num [q0]
  have hq0 : q0 ≠ 0 := by
    norm_num [q0]
  have hsB :
      Summable (fun n : ℕ => psTerm kleinBps q0 n) :=
    summable_psTerm_kleinBps_of_norm_lt_one_of_ne_zero (q := q0) hq hq0
  have hsShift :
      Summable (fun n : ℕ => psTerm kleinBps q0 (n + 4)) := by
    simpa using hsB.comp_injective (add_left_injective 4)
  refine hsShift.norm.congr ?_
  intro n
  simp [psTerm, q0, norm_pow]

theorem kleinDenom_ne_zero_global_of_coeff_majorant_one_div_hundred_lt_1200'
    (hBound100 :
      (∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4))) < (1200 : ℝ)) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_coeff_majorant_one_div_hundred_lt_1200
    summable_coeff_majorant_one_div_hundred hBound100

lemma tsum_norm_psTerm_mul_le
    (φ ψ : PowerSeries ℂ) (q : ℂ)
    (hφ : Summable (fun n : ℕ => ‖psTerm φ q n‖))
    (hψ : Summable (fun n : ℕ => ‖psTerm ψ q n‖)) :
    (∑' n : ℕ, ‖psTerm (φ * ψ) q n‖)
      ≤ (∑' n : ℕ, ‖psTerm φ q n‖) * (∑' n : ℕ, ‖psTerm ψ q n‖) := by
  have hleft : Summable (fun n : ℕ => ‖psTerm (φ * ψ) q n‖) :=
    summable_norm_psTerm_mul (φ := φ) (ψ := ψ) (q := q) hφ hψ
  let c : ℕ → ℝ := fun n =>
    ∑ kl ∈ Finset.antidiagonal n, ‖psTerm φ q kl.1‖ * ‖psTerm ψ q kl.2‖
  have hφR : Summable (fun n : ℕ => ‖(‖psTerm φ q n‖ : ℝ)‖) := by
    simpa [Real.norm_eq_abs] using hφ
  have hψR : Summable (fun n : ℕ => ‖(‖psTerm ψ q n‖ : ℝ)‖) := by
    simpa [Real.norm_eq_abs] using hψ
  have hcSummable : Summable c := by
    simpa [c] using
      (summable_sum_mul_antidiagonal_of_summable_norm'
        (f := fun n : ℕ => ‖psTerm φ q n‖)
        (g := fun n : ℕ => ‖psTerm ψ q n‖)
        hφR hφ hψR hψ)
  have hterm :
      ∀ n : ℕ, ‖psTerm (φ * ψ) q n‖ ≤ c n := by
    intro n
    have hsum :
        psTerm (φ * ψ) q n =
          ∑ kl ∈ Finset.antidiagonal n, psTerm φ q kl.1 * psTerm ψ q kl.2 :=
      psTerm_mul_eq_sum_antidiagonal (φ := φ) (ψ := ψ) (q := q) (n := n)
    calc
      ‖psTerm (φ * ψ) q n‖
          = ‖∑ kl ∈ Finset.antidiagonal n, psTerm φ q kl.1 * psTerm ψ q kl.2‖ := by
              simp [hsum]
      _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖psTerm φ q kl.1 * psTerm ψ q kl.2‖ := by
            exact norm_sum_le _ _
      _ ≤ c n := by
            refine Finset.sum_le_sum ?_
            intro kl hkl
            exact norm_mul_le (psTerm φ q kl.1) (psTerm ψ q kl.2)
  have htsum_le :
      (∑' n : ℕ, ‖psTerm (φ * ψ) q n‖) ≤ ∑' n : ℕ, c n :=
    hleft.tsum_le_tsum hterm hcSummable
  have hmul :
      ((∑' n : ℕ, ‖psTerm φ q n‖) * (∑' n : ℕ, ‖psTerm ψ q n‖))
        = ∑' n : ℕ, c n := by
    simpa [c] using
      (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        (f := fun n : ℕ => ‖psTerm φ q n‖)
        (g := fun n : ℕ => ‖psTerm ψ q n‖)
        hφR hψR)
  exact htsum_le.trans_eq hmul.symm

lemma tsum_norm_psTerm_pow_two_le
    (φ : PowerSeries ℂ) (q : ℂ)
    (hφ : Summable (fun n : ℕ => ‖psTerm φ q n‖)) :
    (∑' n : ℕ, ‖psTerm (φ ^ (2 : ℕ)) q n‖)
      ≤ (∑' n : ℕ, ‖psTerm φ q n‖) ^ (2 : ℕ) := by
  simpa [pow_two] using
    (tsum_norm_psTerm_mul_le (φ := φ) (ψ := φ) (q := q) hφ hφ)

lemma tsum_norm_psTerm_pow_three_le
    (φ : PowerSeries ℂ) (q : ℂ)
    (hφ : Summable (fun n : ℕ => ‖psTerm φ q n‖)) :
    (∑' n : ℕ, ‖psTerm (φ ^ (3 : ℕ)) q n‖)
      ≤ (∑' n : ℕ, ‖psTerm φ q n‖) ^ (3 : ℕ) := by
  have h2 : Summable (fun n : ℕ => ‖psTerm (φ ^ (2 : ℕ)) q n‖) :=
    summable_norm_pow_two (φ := φ) (q := q) hφ
  have hmul :
      (∑' n : ℕ, ‖psTerm ((φ ^ (2 : ℕ)) * φ) q n‖)
        ≤ (∑' n : ℕ, ‖psTerm (φ ^ (2 : ℕ)) q n‖) * (∑' n : ℕ, ‖psTerm φ q n‖) :=
    tsum_norm_psTerm_mul_le (φ := (φ ^ (2 : ℕ))) (ψ := φ) (q := q) h2 hφ
  calc
    (∑' n : ℕ, ‖psTerm (φ ^ (3 : ℕ)) q n‖)
        = (∑' n : ℕ, ‖psTerm ((φ ^ (2 : ℕ)) * φ) q n‖) := by
            simp [pow_succ, mul_assoc]
    _ ≤ (∑' n : ℕ, ‖psTerm (φ ^ (2 : ℕ)) q n‖) * (∑' n : ℕ, ‖psTerm φ q n‖) := hmul
    _ ≤ ((∑' n : ℕ, ‖psTerm φ q n‖) ^ (2 : ℕ)) * (∑' n : ℕ, ‖psTerm φ q n‖) := by
          gcongr
          exact tsum_norm_psTerm_pow_two_le (φ := φ) (q := q) hφ
    _ = (∑' n : ℕ, ‖psTerm φ q n‖) ^ (3 : ℕ) := by
          ring

lemma tsum_norm_psTerm_kleinDps_le_cubes
    (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, ‖psTerm kleinDps q n‖)
      ≤ (∑' n : ℕ, ‖psTerm (qExpansion₁ E4) q n‖) ^ (3 : ℕ)
        + (∑' n : ℕ, ‖psTerm (qExpansion₁ E6) q n‖) ^ (2 : ℕ) := by
  have h4 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E4) q n‖) :=
    summable_norm_qExpansion₁_E4_term (q := q) hq
  have h6 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E6) q n‖) :=
    summable_norm_qExpansion₁_E6_term (q := q) hq
  have h4pow : Summable (fun n : ℕ => ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖) :=
    summable_norm_pow_three (φ := qExpansion₁ E4) (q := q) h4
  have h6pow : Summable (fun n : ℕ => ‖psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n‖) :=
    summable_norm_pow_two (φ := qExpansion₁ E6) (q := q) h6
  have hsub :
      ∀ n : ℕ,
        ‖psTerm kleinDps q n‖
          ≤ ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖
              + ‖psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n‖ := by
    intro n
    have hcoeff :
        psTerm kleinDps q n
          = psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n
              - psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n := by
      simp [kleinDps, kleinDSeries, psTerm, sub_mul]
    calc
      ‖psTerm kleinDps q n‖
          = ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n
              - psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n‖ := by
                simp [hcoeff]
      _ ≤ ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖
            + ‖psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n‖ := by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                (norm_add_le
                  (psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n)
                  (-psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n))
  have hsum_le :
      (∑' n : ℕ, ‖psTerm kleinDps q n‖)
        ≤ (∑' n : ℕ, ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖)
            + (∑' n : ℕ, ‖psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n‖) := by
    have hplusSumm :
        Summable (fun n : ℕ =>
          ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖
            + ‖psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n‖) :=
      h4pow.add h6pow
    have htsum :
        (∑' n : ℕ,
            (‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖
              + ‖psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n‖))
          = (∑' n : ℕ, ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖)
              + (∑' n : ℕ, ‖psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n‖) := by
      simpa using h4pow.tsum_add h6pow
    exact
      ((summable_psTerm_kleinDps (q := q) hq).norm.tsum_le_tsum hsub hplusSumm).trans_eq htsum
  calc
    (∑' n : ℕ, ‖psTerm kleinDps q n‖)
        ≤ (∑' n : ℕ, ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖)
            + (∑' n : ℕ, ‖psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n‖) := hsum_le
    _ ≤ (∑' n : ℕ, ‖psTerm (qExpansion₁ E4) q n‖) ^ (3 : ℕ)
          + (∑' n : ℕ, ‖psTerm (qExpansion₁ E6) q n‖) ^ (2 : ℕ) := by
          gcongr
          · exact tsum_norm_psTerm_pow_three_le (φ := qExpansion₁ E4) (q := q) h4
          · exact tsum_norm_psTerm_pow_two_le (φ := qExpansion₁ E6) (q := q) h6

lemma norm_psTerm_kleinBps_shift_eq_hundred_mul_norm_psTerm_kleinDps_shift (n : ℕ) :
    ‖psTerm kleinBps ((1 / 100 : ℂ)) (n + 4)‖
      = (100 : ℝ) * ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖ := by
  have hmul :
      psTerm kleinBps ((1 / 100 : ℂ)) (n + 4) * ((1 / 100 : ℂ))
        = psTerm kleinDps ((1 / 100 : ℂ)) (n + 5) := by
    simpa [add_assoc] using
      (psTerm_kleinBSeries_mul_q
        (E4ps := qExpansion₁ E4) (E6ps := qExpansion₁ E6) (q := (1 / 100 : ℂ)) (n := n + 4))
  have hq0 : ((1 / 100 : ℂ)) ≠ 0 := by
    norm_num
  have hqinv : ‖((1 / 100 : ℂ))⁻¹‖ = (100 : ℝ) := by
    norm_num
  calc
    ‖psTerm kleinBps ((1 / 100 : ℂ)) (n + 4)‖
        = ‖((1 / 100 : ℂ))⁻¹ * (psTerm kleinBps ((1 / 100 : ℂ)) (n + 4) * ((1 / 100 : ℂ)))‖ := by
            field_simp [hq0]
    _ = ‖((1 / 100 : ℂ))⁻¹ * psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖ := by rw [hmul]
    _ = ‖((1 / 100 : ℂ))⁻¹‖ * ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖ := by
          rw [norm_mul]
    _ = (100 : ℝ) * ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖ := by rw [hqinv]

lemma norm_psTerm_kleinDps_one_hundred_shift_le_one_five_pow_five_mul
    (n : ℕ) :
    ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖
      ≤ ((1 / 5 : ℝ) ^ 5) * ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖ := by
  have hbase :
      ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖
        = ((1 / 5 : ℝ) ^ (n + 5)) * ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖ := by
    have hfac : (1 / 100 : ℝ) = (1 / 5 : ℝ) * (1 / 20 : ℝ) := by
      norm_num
    calc
      ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖
          = ‖kleinDps.coeff (n + 5)‖ * ((1 / 100 : ℝ) ^ (n + 5)) := by
              simp [psTerm, norm_pow]
      _ = ‖kleinDps.coeff (n + 5)‖ * (((1 / 5 : ℝ) * (1 / 20 : ℝ)) ^ (n + 5)) := by
            rw [hfac]
      _ = ‖kleinDps.coeff (n + 5)‖ * ((1 / 5 : ℝ) ^ (n + 5) * (1 / 20 : ℝ) ^ (n + 5)) := by
            rw [mul_pow]
      _ = ((1 / 5 : ℝ) ^ (n + 5)) *
            (‖kleinDps.coeff (n + 5)‖ * ((1 / 20 : ℝ) ^ (n + 5))) := by
            ring
      _ = ((1 / 5 : ℝ) ^ (n + 5)) * ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖ := by
            simp [psTerm, norm_pow]
  have hpow :
      (1 / 5 : ℝ) ^ (n + 5) ≤ (1 / 5 : ℝ) ^ 5 := by
    calc
      (1 / 5 : ℝ) ^ (n + 5) = (1 / 5 : ℝ) ^ n * (1 / 5 : ℝ) ^ 5 := by
        rw [pow_add, mul_comm]
      _ ≤ 1 * (1 / 5 : ℝ) ^ 5 := by
          gcongr
          exact pow_le_one₀ (n := n)
            (by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))
            (by norm_num : (1 / 5 : ℝ) ≤ 1)
      _ = (1 / 5 : ℝ) ^ 5 := by ring
  rw [hbase]
  gcongr

theorem coeff_majorant_one_div_hundred_lt_1200_of_kleinDps_norm_tsum_one_div_twenty_lt_37500
    (hD20 : (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖) < (37500 : ℝ)) :
    (∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4))) < (1200 : ℝ) := by
  have hq100 : ‖((1 / 100 : ℂ))‖ < 1 := by
    norm_num
  have hq20 : ‖((1 / 20 : ℂ))‖ < 1 := by
    norm_num
  have hsD100 :
      Summable (fun n : ℕ => ‖psTerm kleinDps ((1 / 100 : ℂ)) n‖) := by
    simpa using (summable_psTerm_kleinDps (q := (1 / 100 : ℂ)) hq100).norm
  have hsD100tail :
      Summable (fun n : ℕ => ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖) := by
    simpa using hsD100.comp_injective (add_left_injective 5)
  have hsD20 :
      Summable (fun n : ℕ => ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖) := by
    simpa using (summable_psTerm_kleinDps (q := (1 / 20 : ℂ)) hq20).norm
  have hsD20tail :
      Summable (fun n : ℕ => ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖) := by
    simpa using hsD20.comp_injective (add_left_injective 5)
  have hsumD100_le :
      (∑' n : ℕ, ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖)
        ≤ (1 / 5 : ℝ) ^ 5 * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖) := by
    have hcoef : ((1 / 5 : ℝ) ^ 5) = ((5 ^ 5 : ℝ)⁻¹) := by norm_num
    have hterm :
        ∀ n : ℕ,
          ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖
            ≤ ((5 ^ 5 : ℝ)⁻¹) * ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖ := by
      intro n
      simpa [hcoef] using norm_psTerm_kleinDps_one_hundred_shift_le_one_five_pow_five_mul n
    have hle :
        (∑' n : ℕ, ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖)
          ≤ ∑' n : ℕ, ((5 ^ 5 : ℝ)⁻¹) * ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖ :=
      hsD100tail.tsum_le_tsum hterm (hsD20tail.mul_left ((5 ^ 5 : ℝ)⁻¹))
    have hmul :
        (∑' n : ℕ, ((5 ^ 5 : ℝ)⁻¹) * ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖)
          = ((5 ^ 5 : ℝ)⁻¹) * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖) := by
      exact hsD20tail.tsum_mul_left ((5 ^ 5 : ℝ)⁻¹)
    have hle' :
        (∑' n : ℕ, ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖)
          ≤ ((5 ^ 5 : ℝ)⁻¹) * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖) :=
      hle.trans_eq hmul
    simpa [hcoef] using hle'
  have hsumD20tail_le :
      (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖)
        ≤ (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖) := by
    have hsplit := hsD20.sum_add_tsum_nat_add 5
    have hprefix_nonneg :
        0 ≤ ∑ n ∈ Finset.range 5, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖ :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hsumB_eq :
      (∑' n : ℕ, ‖psTerm kleinBps ((1 / 100 : ℂ)) (n + 4)‖)
        = (100 : ℝ) * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖) := by
    have hcongr :
        (fun n : ℕ => ‖psTerm kleinBps ((1 / 100 : ℂ)) (n + 4)‖)
          = (fun n : ℕ => (100 : ℝ) * ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖) := by
      funext n
      exact norm_psTerm_kleinBps_shift_eq_hundred_mul_norm_psTerm_kleinDps_shift n
    rw [hcongr]
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hsD100tail.tsum_mul_left (100 : ℝ))
  have hsumB_le :
      (∑' n : ℕ, ‖psTerm kleinBps ((1 / 100 : ℂ)) (n + 4)‖)
        ≤ (100 : ℝ) * ((1 / 5 : ℝ) ^ 5) * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖) := by
    calc
      (∑' n : ℕ, ‖psTerm kleinBps ((1 / 100 : ℂ)) (n + 4)‖)
          = (100 : ℝ) * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 100 : ℂ)) (n + 5)‖) := hsumB_eq
      _ ≤ (100 : ℝ) * ((1 / 5 : ℝ) ^ 5 * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) (n + 5)‖)) := by
            gcongr
      _ ≤ (100 : ℝ) * ((1 / 5 : ℝ) ^ 5 * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖)) := by
            gcongr
      _ = (100 : ℝ) * ((1 / 5 : ℝ) ^ 5) * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖) := by
            ring
  have hcoeff_eq :
      (∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4)))
        = (∑' n : ℕ, ‖psTerm kleinBps ((1 / 100 : ℂ)) (n + 4)‖) := by
    refine (tsum_congr ?_).symm
    intro n
    simp [psTerm, norm_pow]
  have hconst : (100 : ℝ) * ((1 / 5 : ℝ) ^ 5) = (4 / 125 : ℝ) := by
    norm_num
  have hlt :
      (∑' n : ℕ, ‖psTerm kleinBps ((1 / 100 : ℂ)) (n + 4)‖) < (1200 : ℝ) := by
    have h' :
        (100 : ℝ) * ((1 / 5 : ℝ) ^ 5) * (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖)
          < (1200 : ℝ) := by
      rw [hconst]
      nlinarith [hD20]
    exact lt_of_le_of_lt hsumB_le h'
  rw [hcoeff_eq]
  exact hlt

theorem kleinDenom_ne_zero_global_of_kleinDps_norm_tsum_one_div_twenty_lt_37500
    (hD20 : (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖) < (37500 : ℝ)) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  refine kleinDenom_ne_zero_global_of_coeff_majorant_one_div_hundred_lt_1200' ?_
  exact coeff_majorant_one_div_hundred_lt_1200_of_kleinDps_norm_tsum_one_div_twenty_lt_37500 hD20

lemma step_five_nat (n : ℕ) (hn : 2 ≤ n) : (n + 1) ^ 3 ≤ 5 * n ^ 3 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2n : (2 : ℝ) * ((n : ℝ) + 1) ≤ 3 * (n : ℝ) := by
    nlinarith
  have hlin : ((n : ℝ) + 1) ≤ (3 / 2 : ℝ) * (n : ℝ) := by
    nlinarith [h2n]
  have hpow : (((n : ℝ) + 1) ^ 3) ≤ (((3 / 2 : ℝ) * (n : ℝ)) ^ 3) := by
    gcongr
  have hR : (((n : ℝ) + 1) ^ 3) ≤ (5 : ℝ) * (n : ℝ) ^ 3 := by
    calc
      (((n : ℝ) + 1) ^ 3) ≤ (((3 / 2 : ℝ) * (n : ℝ)) ^ 3) := hpow
      _ = ((3 / 2 : ℝ) ^ 3) * (n : ℝ) ^ 3 := by ring
      _ ≤ (5 : ℝ) * (n : ℝ) ^ 3 := by
            have hconst : ((3 / 2 : ℝ) ^ 3) ≤ (5 : ℝ) := by norm_num
            gcongr
  have hR' : (((n + 1 : ℕ) : ℝ) ^ 3) ≤ (5 : ℝ) * (n : ℝ) ^ 3 := by
    simpa [Nat.cast_add, Nat.cast_one] using hR
  exact_mod_cast hR'

lemma pow_three_le_five_pow {n : ℕ} (hn : 2 ≤ n) : n ^ 3 ≤ 5 ^ n := by
  rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
  induction' m with m hm
  · norm_num
  · have hstep : ((m + 2) + 1) ^ 3 ≤ 5 * (m + 2) ^ 3 :=
      step_five_nat (m + 2) (by omega)
    have hm' : (m + 2) ^ 3 ≤ 5 ^ (m + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm (by omega)
    have hcalc : (m + 2 + 1) ^ 3 ≤ 5 ^ (m + 2 + 1) := by
      calc
        ((m + 2) + 1) ^ 3 ≤ 5 * (m + 2) ^ 3 := hstep
        _ ≤ 5 * 5 ^ (m + 2) := Nat.mul_le_mul_left 5 hm'
        _ = 5 ^ ((m + 2) + 1) := by simp [pow_succ, Nat.mul_comm]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcalc

lemma step_eleven_nat (n : ℕ) (hn : 2 ≤ n) : (n + 1) ^ 5 ≤ 11 * n ^ 5 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2n : (2 : ℝ) * ((n : ℝ) + 1) ≤ 3 * (n : ℝ) := by
    nlinarith
  have hlin : ((n : ℝ) + 1) ≤ (3 / 2 : ℝ) * (n : ℝ) := by
    nlinarith [h2n]
  have hpow : (((n : ℝ) + 1) ^ 5) ≤ (((3 / 2 : ℝ) * (n : ℝ)) ^ 5) := by
    gcongr
  have hR : (((n : ℝ) + 1) ^ 5) ≤ (11 : ℝ) * (n : ℝ) ^ 5 := by
    calc
      (((n : ℝ) + 1) ^ 5) ≤ (((3 / 2 : ℝ) * (n : ℝ)) ^ 5) := hpow
      _ = ((3 / 2 : ℝ) ^ 5) * (n : ℝ) ^ 5 := by ring
      _ ≤ (11 : ℝ) * (n : ℝ) ^ 5 := by
            have hconst : ((3 / 2 : ℝ) ^ 5) ≤ (11 : ℝ) := by norm_num
            gcongr
  have hR' : (((n + 1 : ℕ) : ℝ) ^ 5) ≤ (11 : ℝ) * (n : ℝ) ^ 5 := by
    simpa [Nat.cast_add, Nat.cast_one] using hR
  exact_mod_cast hR'

lemma pow_five_le_eleven_pow {n : ℕ} (hn : 2 ≤ n) : n ^ 5 ≤ 11 ^ n := by
  rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
  induction' m with m hm
  · norm_num
  · have hstep : ((m + 2) + 1) ^ 5 ≤ 11 * (m + 2) ^ 5 :=
      step_eleven_nat (m + 2) (by omega)
    have hm' : (m + 2) ^ 5 ≤ 11 ^ (m + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm (by omega)
    have hcalc : (m + 2 + 1) ^ 5 ≤ 11 ^ (m + 2 + 1) := by
      calc
        ((m + 2) + 1) ^ 5 ≤ 11 * (m + 2) ^ 5 := hstep
        _ ≤ 11 * 11 ^ (m + 2) := Nat.mul_le_mul_left 11 hm'
        _ = 11 ^ ((m + 2) + 1) := by simp [pow_succ, Nat.mul_comm]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcalc

lemma term_pow3_over_twenty_le_quarter_geom (n : ℕ) :
    (((n + 11 : ℕ) : ℝ) ^ 3) * ((1 / 20 : ℝ) ^ (n + 11))
      ≤ (1 / 4 : ℝ) ^ (n + 11) := by
  have hn2 : 2 ≤ n + 11 := by omega
  have hpow : (n + 11 : ℕ) ^ 3 ≤ 5 ^ (n + 11) := pow_three_le_five_pow hn2
  have hpowR : (((n + 11 : ℕ) : ℝ) ^ 3) ≤ (5 : ℝ) ^ (n + 11) := by
    exact_mod_cast hpow
  calc
    (((n + 11 : ℕ) : ℝ) ^ 3) * ((1 / 20 : ℝ) ^ (n + 11))
        ≤ ((5 : ℝ) ^ (n + 11)) * ((1 / 20 : ℝ) ^ (n + 11)) := by
            gcongr
    _ = ((5 : ℝ) * (1 / 20 : ℝ)) ^ (n + 11) := by rw [← mul_pow]
    _ = (1 / 4 : ℝ) ^ (n + 11) := by norm_num

lemma term_pow5_over_twenty_le_eleven_twentieth_geom (n : ℕ) :
    (((n + 11 : ℕ) : ℝ) ^ 5) * ((1 / 20 : ℝ) ^ (n + 11))
      ≤ (11 / 20 : ℝ) ^ (n + 11) := by
  have hn2 : 2 ≤ n + 11 := by omega
  have hpow : (n + 11 : ℕ) ^ 5 ≤ 11 ^ (n + 11) := pow_five_le_eleven_pow hn2
  have hpowR : (((n + 11 : ℕ) : ℝ) ^ 5) ≤ (11 : ℝ) ^ (n + 11) := by
    exact_mod_cast hpow
  calc
    (((n + 11 : ℕ) : ℝ) ^ 5) * ((1 / 20 : ℝ) ^ (n + 11))
        ≤ ((11 : ℝ) ^ (n + 11)) * ((1 / 20 : ℝ) ^ (n + 11)) := by
            gcongr
    _ = ((11 : ℝ) * (1 / 20 : ℝ)) ^ (n + 11) := by rw [← mul_pow]
    _ = (11 / 20 : ℝ) ^ (n + 11) := by ring_nf

private lemma sigma_le_pow_succ (k : ℕ) (n : ℕ) :
    ArithmeticFunction.sigma k n ≤ n ^ (k + 1) := by
  classical
  have hsum :
      ArithmeticFunction.sigma k n ≤ n.divisors.card * (n ^ k) := by
    rw [ArithmeticFunction.sigma_apply]
    have : (∑ d ∈ n.divisors, d ^ k) ≤ ∑ _d ∈ n.divisors, n ^ k := by
      refine Finset.sum_le_sum ?_
      intro d hd
      have hdn : d ≤ n := Nat.divisor_le hd
      exact pow_le_pow_left' hdn k
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hcard : n.divisors.card ≤ n := Nat.card_divisors_le_self n
  calc
    ArithmeticFunction.sigma k n ≤ n.divisors.card * (n ^ k) := hsum
    _ ≤ n * (n ^ k) := Nat.mul_le_mul_right _ hcard
    _ = n ^ (k + 1) := by simp [pow_succ, Nat.mul_comm]

lemma step_twelve_nat (n : ℕ) (hn : 2 ≤ n) : (n + 1) ^ 6 ≤ 12 * n ^ 6 := by
  have h2n : (2 : ℝ) * ((n : ℝ) + 1) ≤ 3 * (n : ℝ) := by
    nlinarith [show (2 : ℝ) ≤ n by exact_mod_cast hn]
  have hpow : (((n : ℝ) + 1) ^ 6) ≤ (((3 / 2 : ℝ) * (n : ℝ)) ^ 6) := by
    have hlin : ((n : ℝ) + 1) ≤ (3 / 2 : ℝ) * (n : ℝ) := by
      nlinarith [h2n]
    gcongr
  have hR : (((n : ℝ) + 1) ^ 6) ≤ (12 : ℝ) * (n : ℝ) ^ 6 := by
    calc
      (((n : ℝ) + 1) ^ 6) ≤ (((3 / 2 : ℝ) * (n : ℝ)) ^ 6) := hpow
      _ = ((3 / 2 : ℝ) ^ 6) * (n : ℝ) ^ 6 := by ring
      _ ≤ (12 : ℝ) * (n : ℝ) ^ 6 := by
            have hconst : ((3 / 2 : ℝ) ^ 6) ≤ (12 : ℝ) := by norm_num
            gcongr
  have hR' : (((n + 1 : ℕ) : ℝ) ^ 6) ≤ (12 : ℝ) * (n : ℝ) ^ 6 := by
    simpa [Nat.cast_add, Nat.cast_one] using hR
  exact_mod_cast hR'

lemma pow_four_le_ten_pow {n : ℕ} (hn : 2 ≤ n) : n ^ 4 ≤ 10 ^ n := by
  have h3 : n ^ 3 ≤ 5 ^ n := pow_three_le_five_pow hn
  have h1 : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
  have hmul : n ^ 3 * n ≤ 5 ^ n * 2 ^ n := Nat.mul_le_mul h3 h1
  calc
    n ^ 4 = n ^ 3 * n := by simp [pow_succ, Nat.mul_comm]
    _ ≤ 5 ^ n * 2 ^ n := hmul
    _ = (5 * 2) ^ n := by rw [← Nat.mul_pow]
    _ = 10 ^ n := by norm_num

lemma pow_six_le_twelve_pow {n : ℕ} (hn : 2 ≤ n) : n ^ 6 ≤ 12 ^ n := by
  rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
  induction' m with m hm
  · norm_num
  · have hstep : ((m + 2) + 1) ^ 6 ≤ 12 * (m + 2) ^ 6 :=
      step_twelve_nat (m + 2) (by omega)
    have hm' : (m + 2) ^ 6 ≤ 12 ^ (m + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm (by omega)
    have hcalc : (m + 2 + 1) ^ 6 ≤ 12 ^ (m + 2 + 1) := by
      calc
        ((m + 2) + 1) ^ 6 ≤ 12 * (m + 2) ^ 6 := hstep
        _ ≤ 12 * 12 ^ (m + 2) := Nat.mul_le_mul_left 12 hm'
        _ = 12 ^ ((m + 2) + 1) := by simp [pow_succ, Nat.mul_comm]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcalc

lemma term_pow4_over_twenty_le_half_geom (n : ℕ) :
    (((n + 11 : ℕ) : ℝ) ^ 4) * ((1 / 20 : ℝ) ^ (n + 11))
      ≤ (1 / 2 : ℝ) ^ (n + 11) := by
  have hn2 : 2 ≤ n + 11 := by omega
  have hpow : (n + 11 : ℕ) ^ 4 ≤ 10 ^ (n + 11) := pow_four_le_ten_pow hn2
  have hpowR : (((n + 11 : ℕ) : ℝ) ^ 4) ≤ (10 : ℝ) ^ (n + 11) := by
    exact_mod_cast hpow
  calc
    (((n + 11 : ℕ) : ℝ) ^ 4) * ((1 / 20 : ℝ) ^ (n + 11))
        ≤ ((10 : ℝ) ^ (n + 11)) * ((1 / 20 : ℝ) ^ (n + 11)) := by
            gcongr
    _ = ((10 : ℝ) * (1 / 20 : ℝ)) ^ (n + 11) := by rw [← mul_pow]
    _ = (1 / 2 : ℝ) ^ (n + 11) := by norm_num

lemma term_pow6_over_twenty_le_three_fifth_geom (n : ℕ) :
    (((n + 11 : ℕ) : ℝ) ^ 6) * ((1 / 20 : ℝ) ^ (n + 11))
      ≤ (3 / 5 : ℝ) ^ (n + 11) := by
  have hn2 : 2 ≤ n + 11 := by omega
  have hpow : (n + 11 : ℕ) ^ 6 ≤ 12 ^ (n + 11) := pow_six_le_twelve_pow hn2
  have hpowR : (((n + 11 : ℕ) : ℝ) ^ 6) ≤ (12 : ℝ) ^ (n + 11) := by
    exact_mod_cast hpow
  calc
    (((n + 11 : ℕ) : ℝ) ^ 6) * ((1 / 20 : ℝ) ^ (n + 11))
        ≤ ((12 : ℝ) ^ (n + 11)) * ((1 / 20 : ℝ) ^ (n + 11)) := by
            gcongr
    _ = ((12 : ℝ) * (1 / 20 : ℝ)) ^ (n + 11) := by rw [← mul_pow]
    _ = (3 / 5 : ℝ) ^ (n + 11) := by ring_nf

lemma tsum_norm_psTerm_qExpansion₁_E4_one_div_twenty_lt_twenty_one :
    (∑' n : ℕ, ‖psTerm (qExpansion₁ E4) ((1 / 20 : ℂ)) n‖) < (21 : ℝ) := by
  let f4 : ℕ → ℝ := fun n => ‖psTerm (qExpansion₁ E4) ((1 / 20 : ℂ)) n‖
  have hq20 : ‖((1 / 20 : ℂ))‖ < 1 := by
    norm_num
  have hs4 : Summable f4 := by
    simpa [f4] using (summable_norm_qExpansion₁_E4_term (q := (1 / 20 : ℂ)) hq20)
  have hs4tail : Summable (fun n : ℕ => f4 (n + 11)) := by
    simpa [f4] using hs4.comp_injective (add_left_injective 11)
  have hprefix_lt :
      (∑ n ∈ Finset.range 11, f4 n) < (20 : ℝ) := by
    simp [f4, Finset.sum_range_succ, qExpansion₁_E4_eq_expected, psTerm]
    norm_num
  have hterm :
      ∀ n : ℕ, f4 (n + 11) ≤ (240 : ℝ) * ((1 / 2 : ℝ) ^ (n + 11)) := by
    intro n
    have hsigma :
        (ArithmeticFunction.sigma 3 (n + 11) : ℝ) ≤ ((n + 11 : ℕ) : ℝ) ^ 4 := by
      have hs' : ArithmeticFunction.sigma 3 (n + 11) ≤ (n + 11) ^ (3 + 1) :=
        sigma_le_pow_succ 3 (n + 11)
      exact_mod_cast hs'
    have hcoeff :
        ‖(qExpansion₁ E4).coeff (n + 11)‖ ≤ (240 : ℝ) * (((n + 11 : ℕ) : ℝ) ^ 4) := by
      have hcn :
          (qExpansion₁ E4).coeff (n + 11) =
            (240 : ℂ) * (ArithmeticFunction.sigma 3 (n + 11) : ℂ) := by
        have hnz : (n + 11 : ℕ) ≠ 0 := by omega
        simpa [qExpansion₁_E4_eq_expected] using
          (E4_q_expected_coeff_of_ne_zero (n := n + 11) hnz)
      have : ‖(qExpansion₁ E4).coeff (n + 11)‖
          ≤ (240 : ℝ) * (ArithmeticFunction.sigma 3 (n + 11) : ℝ) := by
        simp [hcn]
      calc
        ‖(qExpansion₁ E4).coeff (n + 11)‖
            ≤ (240 : ℝ) * (ArithmeticFunction.sigma 3 (n + 11) : ℝ) := this
        _ ≤ (240 : ℝ) * (((n + 11 : ℕ) : ℝ) ^ 4) := by gcongr
    have hpoly :
        (((n + 11 : ℕ) : ℝ) ^ 4) * ((1 / 20 : ℝ) ^ (n + 11))
          ≤ (1 / 2 : ℝ) ^ (n + 11) :=
      term_pow4_over_twenty_le_half_geom n
    calc
      f4 (n + 11)
          = ‖(qExpansion₁ E4).coeff (n + 11)‖ * ((1 / 20 : ℝ) ^ (n + 11)) := by
              simp [f4, psTerm, norm_pow]
      _ ≤ ((240 : ℝ) * (((n + 11 : ℕ) : ℝ) ^ 4)) * ((1 / 20 : ℝ) ^ (n + 11)) := by
            gcongr
      _ = (240 : ℝ) * ((((n + 11 : ℕ) : ℝ) ^ 4) * ((1 / 20 : ℝ) ^ (n + 11))) := by ring
      _ ≤ (240 : ℝ) * ((1 / 2 : ℝ) ^ (n + 11)) := by gcongr
  have hsGeomShift : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ (n + 11))) := by
    simpa using
      (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).comp_injective
        (add_left_injective 11)
  have hsGeomMul : Summable (fun n : ℕ => (240 : ℝ) * ((1 / 2 : ℝ) ^ (n + 11))) :=
    hsGeomShift.mul_left (240 : ℝ)
  have htail_le :
      (∑' n : ℕ, f4 (n + 11))
        ≤ ∑' n : ℕ, (240 : ℝ) * ((1 / 2 : ℝ) ^ (n + 11)) :=
    hs4tail.tsum_le_tsum hterm hsGeomMul
  have hgeom_eq :
      (∑' n : ℕ, (240 : ℝ) * ((1 / 2 : ℝ) ^ (n + 11)))
        = (240 : ℝ) * (((1 / 2 : ℝ) ^ 11) * ((1 - (1 / 2 : ℝ))⁻¹)) := by
    calc
      (∑' n : ℕ, (240 : ℝ) * ((1 / 2 : ℝ) ^ (n + 11)))
          = (240 : ℝ) * (∑' n : ℕ, ((1 / 2 : ℝ) ^ (n + 11))) := by
              exact hsGeomShift.tsum_mul_left (240 : ℝ)
      _ = (240 : ℝ) * (((1 / 2 : ℝ) ^ 11) * (∑' n : ℕ, ((1 / 2 : ℝ) ^ n))) := by
            congr 1
            calc
              (∑' n : ℕ, ((1 / 2 : ℝ) ^ (n + 11)))
                  = ∑' n : ℕ, ((1 / 2 : ℝ) ^ 11) * ((1 / 2 : ℝ) ^ n) := by
                      refine tsum_congr ?_
                      intro n
                      rw [pow_add]
                      ring
              _ = ((1 / 2 : ℝ) ^ 11) * (∑' n : ℕ, ((1 / 2 : ℝ) ^ n)) := by
                    exact (summable_geometric_of_lt_one (r := (1 / 2 : ℝ))
                      (by norm_num) (by norm_num)).tsum_mul_left _
      _ = (240 : ℝ) * (((1 / 2 : ℝ) ^ 11) * ((1 - (1 / 2 : ℝ))⁻¹)) := by
            rw [tsum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)]
  have htail_lt_one :
      (∑' n : ℕ, f4 (n + 11)) < (1 : ℝ) := by
    refine lt_of_le_of_lt htail_le ?_
    rw [hgeom_eq]
    norm_num
  have hsplit :
      (∑' n : ℕ, f4 n)
        = (∑ n ∈ Finset.range 11, f4 n) + (∑' n : ℕ, f4 (n + 11)) := by
    simpa [add_comm, add_left_comm, add_assoc] using (hs4.sum_add_tsum_nat_add 11).symm
  rw [hsplit]
  nlinarith [hprefix_lt, htail_lt_one]

lemma tsum_norm_psTerm_qExpansion₁_E6_one_div_twenty_lt_ninety_five :
    (∑' n : ℕ, ‖psTerm (qExpansion₁ E6) ((1 / 20 : ℂ)) n‖) < (95 : ℝ) := by
  let f6 : ℕ → ℝ := fun n => ‖psTerm (qExpansion₁ E6) ((1 / 20 : ℂ)) n‖
  have hq20 : ‖((1 / 20 : ℂ))‖ < 1 := by
    norm_num
  have hs6 : Summable f6 := by
    simpa [f6] using (summable_norm_qExpansion₁_E6_term (q := (1 / 20 : ℂ)) hq20)
  have hs6tail : Summable (fun n : ℕ => f6 (n + 11)) := by
    simpa [f6] using hs6.comp_injective (add_left_injective 11)
  have hprefix_lt :
      (∑ n ∈ Finset.range 11, f6 n) < (90 : ℝ) := by
    simp [f6, Finset.sum_range_succ, qExpansion₁_E6_eq_expected, psTerm]
    norm_num
  have hterm :
      ∀ n : ℕ, f6 (n + 11) ≤ (504 : ℝ) * ((3 / 5 : ℝ) ^ (n + 11)) := by
    intro n
    have hsigma :
        (ArithmeticFunction.sigma 5 (n + 11) : ℝ) ≤ ((n + 11 : ℕ) : ℝ) ^ 6 := by
      have hs' : ArithmeticFunction.sigma 5 (n + 11) ≤ (n + 11) ^ (5 + 1) :=
        sigma_le_pow_succ 5 (n + 11)
      exact_mod_cast hs'
    have hcoeff :
        ‖(qExpansion₁ E6).coeff (n + 11)‖ ≤ (504 : ℝ) * (((n + 11 : ℕ) : ℝ) ^ 6) := by
      have hcn :
          (qExpansion₁ E6).coeff (n + 11) =
            (-504 : ℂ) * (ArithmeticFunction.sigma 5 (n + 11) : ℂ) := by
        have hnz : (n + 11 : ℕ) ≠ 0 := by omega
        simpa [qExpansion₁_E6_eq_expected] using
          (E6_q_expected_coeff_of_ne_zero (n := n + 11) hnz)
      have : ‖(qExpansion₁ E6).coeff (n + 11)‖
          ≤ (504 : ℝ) * (ArithmeticFunction.sigma 5 (n + 11) : ℝ) := by
        simp [hcn]
      calc
        ‖(qExpansion₁ E6).coeff (n + 11)‖
            ≤ (504 : ℝ) * (ArithmeticFunction.sigma 5 (n + 11) : ℝ) := this
        _ ≤ (504 : ℝ) * (((n + 11 : ℕ) : ℝ) ^ 6) := by gcongr
    have hpoly :
        (((n + 11 : ℕ) : ℝ) ^ 6) * ((1 / 20 : ℝ) ^ (n + 11))
          ≤ (3 / 5 : ℝ) ^ (n + 11) :=
      term_pow6_over_twenty_le_three_fifth_geom n
    calc
      f6 (n + 11)
          = ‖(qExpansion₁ E6).coeff (n + 11)‖ * ((1 / 20 : ℝ) ^ (n + 11)) := by
              simp [f6, psTerm, norm_pow]
      _ ≤ ((504 : ℝ) * (((n + 11 : ℕ) : ℝ) ^ 6)) * ((1 / 20 : ℝ) ^ (n + 11)) := by
            gcongr
      _ = (504 : ℝ) * ((((n + 11 : ℕ) : ℝ) ^ 6) * ((1 / 20 : ℝ) ^ (n + 11))) := by ring
      _ ≤ (504 : ℝ) * ((3 / 5 : ℝ) ^ (n + 11)) := by gcongr
  have hsGeomShift : Summable (fun n : ℕ => ((3 / 5 : ℝ) ^ (n + 11))) := by
    simpa using
      (summable_geometric_of_lt_one (r := (3 / 5 : ℝ)) (by norm_num) (by norm_num)).comp_injective
        (add_left_injective 11)
  have hsGeomMul : Summable (fun n : ℕ => (504 : ℝ) * ((3 / 5 : ℝ) ^ (n + 11))) :=
    hsGeomShift.mul_left (504 : ℝ)
  have htail_le :
      (∑' n : ℕ, f6 (n + 11))
        ≤ ∑' n : ℕ, (504 : ℝ) * ((3 / 5 : ℝ) ^ (n + 11)) :=
    hs6tail.tsum_le_tsum hterm hsGeomMul
  have hgeom_eq :
      (∑' n : ℕ, (504 : ℝ) * ((3 / 5 : ℝ) ^ (n + 11)))
        = (504 : ℝ) * (((3 / 5 : ℝ) ^ 11) * ((1 - (3 / 5 : ℝ))⁻¹)) := by
    calc
      (∑' n : ℕ, (504 : ℝ) * ((3 / 5 : ℝ) ^ (n + 11)))
          = (504 : ℝ) * (∑' n : ℕ, ((3 / 5 : ℝ) ^ (n + 11))) := by
              exact hsGeomShift.tsum_mul_left (504 : ℝ)
      _ = (504 : ℝ) * (((3 / 5 : ℝ) ^ 11) * (∑' n : ℕ, ((3 / 5 : ℝ) ^ n))) := by
            congr 1
            calc
              (∑' n : ℕ, ((3 / 5 : ℝ) ^ (n + 11)))
                  = ∑' n : ℕ, ((3 / 5 : ℝ) ^ 11) * ((3 / 5 : ℝ) ^ n) := by
                      refine tsum_congr ?_
                      intro n
                      rw [pow_add]
                      ring
              _ = ((3 / 5 : ℝ) ^ 11) * (∑' n : ℕ, ((3 / 5 : ℝ) ^ n)) := by
                    exact (summable_geometric_of_lt_one (r := (3 / 5 : ℝ))
                      (by norm_num) (by norm_num)).tsum_mul_left _
      _ = (504 : ℝ) * (((3 / 5 : ℝ) ^ 11) * ((1 - (3 / 5 : ℝ))⁻¹)) := by
            rw [tsum_geometric_of_lt_one (r := (3 / 5 : ℝ)) (by norm_num) (by norm_num)]
  have htail_lt_five :
      (∑' n : ℕ, f6 (n + 11)) < (5 : ℝ) := by
    refine lt_of_le_of_lt htail_le ?_
    rw [hgeom_eq]
    norm_num
  have hsplit :
      (∑' n : ℕ, f6 n)
        = (∑ n ∈ Finset.range 11, f6 n) + (∑' n : ℕ, f6 (n + 11)) := by
    simpa [add_comm, add_left_comm, add_assoc] using (hs6.sum_add_tsum_nat_add 11).symm
  rw [hsplit]
  nlinarith [hprefix_lt, htail_lt_five]

theorem kleinDps_norm_tsum_one_div_twenty_lt_37500 :
    (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖) < (37500 : ℝ) := by
  have hq20 : ‖((1 / 20 : ℂ))‖ < 1 := by
    norm_num
  have hDle :
      (∑' n : ℕ, ‖psTerm kleinDps ((1 / 20 : ℂ)) n‖)
        ≤ (∑' n : ℕ, ‖psTerm (qExpansion₁ E4) ((1 / 20 : ℂ)) n‖) ^ (3 : ℕ)
          + (∑' n : ℕ, ‖psTerm (qExpansion₁ E6) ((1 / 20 : ℂ)) n‖) ^ (2 : ℕ) :=
    tsum_norm_psTerm_kleinDps_le_cubes (q := (1 / 20 : ℂ)) hq20
  have hE4le :
      (∑' n : ℕ, ‖psTerm (qExpansion₁ E4) ((1 / 20 : ℂ)) n‖) ≤ (21 : ℝ) :=
    (le_of_lt tsum_norm_psTerm_qExpansion₁_E4_one_div_twenty_lt_twenty_one)
  have hE6le :
      (∑' n : ℕ, ‖psTerm (qExpansion₁ E6) ((1 / 20 : ℂ)) n‖) ≤ (95 : ℝ) :=
    (le_of_lt tsum_norm_psTerm_qExpansion₁_E6_one_div_twenty_lt_ninety_five)
  have hBound :
      (∑' n : ℕ, ‖psTerm (qExpansion₁ E4) ((1 / 20 : ℂ)) n‖) ^ (3 : ℕ)
        + (∑' n : ℕ, ‖psTerm (qExpansion₁ E6) ((1 / 20 : ℂ)) n‖) ^ (2 : ℕ)
        ≤ (21 : ℝ) ^ (3 : ℕ) + (95 : ℝ) ^ (2 : ℕ) := by
    gcongr
  have hNum : (21 : ℝ) ^ (3 : ℕ) + (95 : ℝ) ^ (2 : ℕ) < (37500 : ℝ) := by
    norm_num
  exact lt_of_le_of_lt (hDle.trans hBound) hNum

theorem kleinDenom_ne_zero_global :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  exact
    kleinDenom_ne_zero_global_of_kleinDps_norm_tsum_one_div_twenty_lt_37500
      kleinDps_norm_tsum_one_div_twenty_lt_37500

end HeytingLean.Moonshine.Modular
