import HeytingLean.Moonshine.Modular.KleinBfunExtTruncation
import HeytingLean.Moonshine.Modular.KleinDenomCuspBridge
import HeytingLean.Moonshine.Modular.KleinDenominatorGlobalReduction
import HeytingLean.Moonshine.Modular.FundamentalDomainQBounds

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

open scoped MatrixGroups

/-- Degree-3 truncation of `kleinBfunExt` at `q = 0`. -/
def kleinB_trunc_poly (q : ℂ) : ℂ :=
  (1728 : ℂ)
    + (-41472 : ℂ) * q
    + (435456 : ℂ) * q ^ 2
    + (-2543616 : ℂ) * q ^ 3

lemma norm_kleinB_trunc_poly_ge_1228 {q : ℂ} (hq : ‖q‖ ≤ (1 / 100 : ℝ)) :
    (1228 : ℝ) ≤ ‖kleinB_trunc_poly q‖ := by
  let a : ℂ := (-41472 : ℂ) * q
  let b : ℂ := (435456 : ℂ) * q ^ 2
  let c : ℂ := (-2543616 : ℂ) * q ^ 3
  have ha : ‖a‖ ≤ (415 : ℝ) := by
    have hm : ‖a‖ = (41472 : ℝ) * ‖q‖ := by
      dsimp [a]
      rw [norm_mul]
      norm_num
    rw [hm]
    nlinarith
  have hb : ‖b‖ ≤ (44 : ℝ) := by
    have hq2 : ‖q ^ 2‖ ≤ (1 / 100 : ℝ) ^ 2 := by
      have hq_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
      have hq2' : ‖q‖ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith [hq, hq_nonneg]
      simpa [norm_pow] using hq2'
    have hm : ‖b‖ = (435456 : ℝ) * ‖q ^ 2‖ := by
      dsimp [b]
      rw [norm_mul]
      norm_num
    rw [hm]
    nlinarith
  have hc : ‖c‖ ≤ (3 : ℝ) := by
    have hq3 : ‖q ^ 3‖ ≤ (1 / 100 : ℝ) ^ 3 := by
      have hq_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
      have hq2' : ‖q‖ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith [hq, hq_nonneg]
      have hq3' : ‖q‖ ^ 3 ≤ (1 / 100 : ℝ) ^ 3 := by
        calc
          ‖q‖ ^ 3 = ‖q‖ ^ 2 * ‖q‖ := by ring
          _ ≤ ((1 / 100 : ℝ) ^ 2) * ‖q‖ := by gcongr
          _ ≤ ((1 / 100 : ℝ) ^ 2) * (1 / 100 : ℝ) := by gcongr
          _ = (1 / 100 : ℝ) ^ 3 := by ring
      simpa [norm_pow] using hq3'
    have hm : ‖c‖ = (2543616 : ℝ) * ‖q ^ 3‖ := by
      dsimp [c]
      rw [norm_mul]
      norm_num
    rw [hm]
    nlinarith
  have habc : ‖a + b + c‖ ≤ (500 : ℝ) := by
    calc
      ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 500 := by nlinarith
  have hsub : ‖(1728 : ℂ)‖ - ‖a + b + c‖ ≤ ‖(1728 : ℂ) + (a + b + c)‖ := by
    let y : ℂ := -c + (-b + -a)
    have hy : y = -(a + b + c) := by
      dsimp [y]
      ring
    have hraw : ‖(1728 : ℂ)‖ - ‖y‖ ≤ ‖(1728 : ℂ) - y‖ :=
      norm_sub_norm_le (1728 : ℂ) y
    have hyNorm : ‖y‖ = ‖a + b + c‖ := by
      rw [hy]
      simpa using (norm_neg (a + b + c))
    have hyRhs : ‖(1728 : ℂ) - y‖ = ‖(1728 : ℂ) + (a + b + c)‖ := by
      rw [hy]
      simp [sub_eq_add_neg]
    calc
      ‖(1728 : ℂ)‖ - ‖a + b + c‖ = ‖(1728 : ℂ)‖ - ‖y‖ := by rw [hyNorm]
      _ ≤ ‖(1728 : ℂ) - y‖ := hraw
      _ = ‖(1728 : ℂ) + (a + b + c)‖ := hyRhs
  have hmain : (1228 : ℝ) ≤ ‖(1728 : ℂ) + (a + b + c)‖ := by
    have h1728 : ‖(1728 : ℂ)‖ = (1728 : ℝ) := by norm_num
    rw [h1728] at hsub
    nlinarith
  simpa [kleinB_trunc_poly, a, b, c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain

lemma kleinBfunExt_ne_zero_of_norm_le_one_div_hundred_of_tail_lt_1200
    {q : ℂ} (hq : ‖q‖ ≤ (1 / 100 : ℝ)) (hq_lt : ‖q‖ < 1) (hq0 : q ≠ 0)
    (htail : ‖q ^ 4 * kleinB_tail_eval q‖ < (1200 : ℝ)) :
    kleinBfunExt q ≠ 0 := by
  let p : ℂ := kleinB_trunc_poly q
  let t : ℂ := q ^ 4 * kleinB_tail_eval q
  have hp1228 : (1228 : ℝ) ≤ ‖p‖ := by
    simpa [p] using norm_kleinB_trunc_poly_ge_1228 (q := q) hq
  have hsplit : kleinBfunExt q = p + t := by
    simpa [p, t, kleinB_trunc_poly, add_assoc, add_left_comm, add_comm] using
      (kleinBfunExt_eq_trunc_of_norm_lt_one_of_ne_zero (q := q) hq_lt hq0)
  intro hzero
  have hpAddZero : p + t = 0 := by
    calc
      p + t = kleinBfunExt q := by simp [hsplit]
      _ = 0 := hzero
  have hpneg : p = -t := eq_neg_of_add_eq_zero_left hpAddZero
  have hpnorm : ‖p‖ < (1200 : ℝ) := by
    calc
      ‖p‖ = ‖-t‖ := by simp [hpneg]
      _ = ‖t‖ := by simp
      _ < 1200 := by simpa [t] using htail
  linarith

theorem kleinDenom_ne_zero_on_fd_of_tail_lt_1200
    (hTailFd : ∀ τ : ℍ, τ ∈ ModularGroup.fd →
      ‖(q τ) ^ 4 * kleinB_tail_eval (q τ)‖ < (1200 : ℝ))
    (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    kleinDenom τ ≠ 0 := by
  have hB :
      kleinBfunExt (q τ) ≠ 0 :=
    kleinBfunExt_ne_zero_of_norm_le_one_div_hundred_of_tail_lt_1200
      (q := q τ)
      (hq := norm_q_le_one_div_hundred_of_mem_fd (τ := τ) hτ)
      (hq_lt := norm_q_lt_one τ)
      (hq0 := q_ne_zero τ)
      (htail := hTailFd τ hτ)
  exact (kleinDenom_ne_zero_iff_kleinBfunExt_ne_zero (τ := τ)).2 hB

theorem kleinDenom_ne_zero_global_of_fd_tail_lt_1200
    (hTailFd : ∀ τ : ℍ, τ ∈ ModularGroup.fd →
      ‖(q τ) ^ 4 * kleinB_tail_eval (q τ)‖ < (1200 : ℝ)) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  refine kleinDenom_ne_zero_of_nonzero_on_fd ?_
  intro τ hτ
  exact kleinDenom_ne_zero_on_fd_of_tail_lt_1200 hTailFd τ hτ

end HeytingLean.Moonshine.Modular
