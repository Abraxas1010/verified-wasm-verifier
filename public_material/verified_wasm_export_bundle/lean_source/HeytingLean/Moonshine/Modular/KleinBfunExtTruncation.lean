import HeytingLean.Moonshine.Modular.KleinBfunExtExplicitNonvanishing
import HeytingLean.Moonshine.Modular.KleinDenominatorCoefficients
import HeytingLean.Moonshine.Modular.QParam

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open scoped BigOperators
open UpperHalfPlane

/-!
## Explicit Truncation for `kleinBfunExt`

This packages the first low-order coefficients of `kleinBps` into an exact identity
`kleinBfunExt = (degree-3 truncation) + q^4 * tail` on the punctured unit disc.
-/

/-- Tail series for `kleinBps` after removing the first 4 coefficients. -/
noncomputable def kleinB_tail_eval (q : ℂ) : ℂ :=
  ∑' n : ℕ, (kleinBps.coeff (n + 4)) * q ^ n

lemma kleinBfunExt_eq_trunc_of_norm_lt_one_of_ne_zero (q : ℂ)
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    kleinBfunExt q =
      (1728 : ℂ)
        + (-41472 : ℂ) * q
        + (435456 : ℂ) * q ^ 2
        + (-2543616 : ℂ) * q ^ 3
        + q ^ 4 * kleinB_tail_eval q := by
  let fD : ℕ → ℂ := fun n => psTerm kleinDps q n
  let fB : ℕ → ℂ := fun n => psTerm kleinBps q n
  have hsD : Summable fD := by
    simpa [fD] using (summable_psTerm_kleinDps (q := q) hq)
  have hsDsucc : Summable (fun n : ℕ => fD (n + 1)) :=
    hsD.comp_injective (add_left_injective 1)
  have hsB : Summable fB := by
    have hcongr : ∀ n : ℕ, (q⁻¹) * fD (n + 1) = fB n := by
      intro n
      calc
        (q⁻¹) * fD (n + 1) = q⁻¹ * (fB n * q) := by
          simp [fB, fD, kleinBps, kleinDps, psTerm_kleinBSeries_mul_q]
        _ = fB n := by
          field_simp [hq0, fB]
    exact (hsDsucc.mul_left q⁻¹).congr hcongr
  have hsplit :
      (∑' n : ℕ, fB n) = (∑ n ∈ Finset.range 4, fB n) + (∑' n : ℕ, fB (n + 4)) := by
    simpa using (hsB.sum_add_tsum_nat_add 4).symm
  have hsum4 :
      (∑ n ∈ Finset.range 4, fB n) =
        (1728 : ℂ)
          + (-41472 : ℂ) * q
          + (435456 : ℂ) * q ^ 2
          + (-2543616 : ℂ) * q ^ 3 := by
    have hsum :
        (∑ n ∈ Finset.range 4, fB n) = fB 0 + fB 1 + fB 2 + fB 3 := by
      simp [Finset.sum_range_succ, add_assoc]
    have h0 : fB 0 = (1728 : ℂ) := by
      calc
        fB 0 = kleinBps.coeff 0 := by simp [fB, psTerm]
        _ = (1728 : ℂ) := kleinBps_coeff_zero
    have h1 : fB 1 = (-41472 : ℂ) * q := by
      calc
        fB 1 = kleinBps.coeff 1 * q := by simp [fB, psTerm]
        _ = (-41472 : ℂ) * q := by rw [kleinBps_coeff_one]
    have h2 : fB 2 = (435456 : ℂ) * q ^ 2 := by
      calc
        fB 2 = kleinBps.coeff 2 * q ^ 2 := by simp [fB, psTerm]
        _ = (435456 : ℂ) * q ^ 2 := by rw [kleinBps_coeff_two]
    have h3 : fB 3 = (-2543616 : ℂ) * q ^ 3 := by
      calc
        fB 3 = kleinBps.coeff 3 * q ^ 3 := by simp [fB, psTerm]
        _ = (-2543616 : ℂ) * q ^ 3 := by rw [kleinBps_coeff_three]
    rw [hsum]
    rw [h0, h1, h2, h3]
  let g : ℕ → ℂ := fun n => (kleinBps.coeff (n + 4)) * q ^ n
  have hsBtail : Summable (fun n : ℕ => fB (n + 4)) :=
    hsB.comp_injective (add_left_injective 4)
  have hsG : Summable g := by
    have hq4 : (q ^ 4 : ℂ) ≠ 0 := pow_ne_zero 4 hq0
    have hcongr : ∀ n : ℕ, (q ^ 4)⁻¹ * fB (n + 4) = g n := by
      intro n
      calc
        (q ^ 4)⁻¹ * fB (n + 4) = (q ^ 4)⁻¹ * (q ^ 4 * g n) := by
          simp [g, fB, psTerm, pow_add, mul_assoc, mul_left_comm, mul_comm]
        _ = g n := by
          field_simp [hq4]
    exact (hsBtail.mul_left ((q ^ 4)⁻¹)).congr hcongr
  have htail :
      (∑' n : ℕ, fB (n + 4)) = q ^ 4 * kleinB_tail_eval q := by
    calc
      (∑' n : ℕ, fB (n + 4)) = ∑' n : ℕ, q ^ 4 * g n := by
        refine tsum_congr (fun n => ?_)
        simp [g, fB, psTerm, pow_add, mul_assoc, mul_left_comm, mul_comm]
      _ = q ^ 4 * (∑' n : ℕ, g n) := by
        simpa using (hsG.tsum_mul_left (q ^ 4))
      _ = q ^ 4 * kleinB_tail_eval q := by
        simp [kleinB_tail_eval, g]
  have htsum :
      kleinBfunExt q = (∑' n : ℕ, fB n) := by
    simpa [fB] using (kleinBfunExt_eq_tsum_psTerm_kleinBps (q := q) hq hq0)
  calc
    kleinBfunExt q = (∑' n : ℕ, fB n) := htsum
    _ = (∑ n ∈ Finset.range 4, fB n) + (∑' n : ℕ, fB (n + 4)) := hsplit
    _ = ((1728 : ℂ)
          + (-41472 : ℂ) * q
          + (435456 : ℂ) * q ^ 2
          + (-2543616 : ℂ) * q ^ 3) + q ^ 4 * kleinB_tail_eval q := by
          rw [hsum4, htail]
    _ = (1728 : ℂ)
          + (-41472 : ℂ) * q
          + (435456 : ℂ) * q ^ 2
          + (-2543616 : ℂ) * q ^ 3
          + q ^ 4 * kleinB_tail_eval q := by ring

lemma kleinBfunExt_q_of_mem_fd_eq_trunc (τ : ℍ) (_hτ : τ ∈ ModularGroup.fd) :
    kleinBfunExt (q τ) =
      (1728 : ℂ)
        + (-41472 : ℂ) * (q τ)
        + (435456 : ℂ) * (q τ) ^ 2
        + (-2543616 : ℂ) * (q τ) ^ 3
        + (q τ) ^ 4 * kleinB_tail_eval (q τ) := by
  exact kleinBfunExt_eq_trunc_of_norm_lt_one_of_ne_zero
    (q := q τ) (hq := norm_q_lt_one τ) (hq0 := q_ne_zero τ)

end HeytingLean.Moonshine.Modular
