import HeytingLean.Moonshine.Modular.KleinJ0LaurentEval

import Mathlib.RingTheory.HahnSeries.Multiplication

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open scoped BigOperators
open scoped Topology
open Filter

/-!
## Laurent-at-infinity expansion for `kleinJ₀`

We already have:
- formal coefficient matches in `KleinJ0Laurent.lean`:
  `kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q`,
- an analytic bridge on a punctured neighborhood of `0`:
  `eventually_kleinJ₀_cusp_eq_kleinJ₀_qLaurent_eval`.

This file packages these into an explicit "truncation + tail" Laurent statement near `q = 0`,
showing the first coefficients match `JSeries.J_q`.
-/

private def Aps : PowerSeries ℂ :=
  kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)

private def kJ : HahnSeries ℤ ℂ :=
  HahnSeries.single (-1 : ℤ) (1 : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ Aps

private def kJ0 : HahnSeries ℤ ℂ :=
  kJ - HahnSeries.C (744 : ℂ)

private lemma kJ_eq_kleinJ : kJ = kleinJ_qLaurent (qExpansion₁ E4) (qExpansion₁ E6) := by
  rfl

private lemma kJ0_eq_kleinJ0 : kJ0 = kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6) := by
  rfl

private lemma coeff_kJ_shift (n : ℕ) :
    kJ.coeff ((n : ℤ) + (-1 : ℤ)) = (Aps.coeff n) := by
  -- Avoid `simp`-unfolding `Aps` inside `HahnSeries.ofPowerSeries` by rewriting explicitly.
  change
      (HahnSeries.single (-1 : ℤ) (1 : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ Aps).coeff
          ((n : ℤ) + (-1 : ℤ)) =
        Aps.coeff n
  have h :=
    (HahnSeries.coeff_single_mul_add (r := (1 : ℂ))
      (x := HahnSeries.ofPowerSeries ℤ ℂ Aps) (a := (n : ℤ)) (b := (-1 : ℤ)))
  -- Rewrite with the shift lemma, then identify the `ofPowerSeries` coefficient.
  rw [h]
  have hx : (HahnSeries.ofPowerSeries ℤ ℂ Aps).coeff (n : ℤ) = Aps.coeff n := by
    -- `ofPowerSeries_apply_coeff` uses a `ℕ` index; coercions identify it with `(n : ℤ)`.
    simpa using (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (R := ℂ) (x := Aps) n)
  -- Finish.
  rw [hx]
  simp

private lemma coeff_Aps_0 : Aps.coeff 0 = (1 : ℂ) := by
  have hk : (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff (-1 : ℤ) = (1 : ℂ) := by
    simpa [coeff_J_q_neg1] using (kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q).1
  have hk0 : kJ0.coeff (-1 : ℤ) = (1 : ℂ) := by
    simpa [kJ0_eq_kleinJ0] using hk
  have hkshift : kJ0.coeff (-1 : ℤ) = kJ.coeff (-1 : ℤ) := by
    simp [kJ0, kJ]
  -- Now use the `-1` coefficient shift (`n = 0`).
  have : kJ.coeff (-1 : ℤ) = Aps.coeff 0 := by
    simpa using (coeff_kJ_shift (n := 0))
  exact (this.symm.trans (hkshift.symm.trans hk0))

private lemma coeff_Aps_1 : Aps.coeff 1 = (744 : ℂ) := by
  have hk :
      (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff (0 : ℤ) = (0 : ℂ) := by
    simpa [coeff_J_q_0] using (kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q).2.1
  have hk' : kJ0.coeff (0 : ℤ) = (0 : ℂ) := by simpa [kJ0_eq_kleinJ0] using hk
  have hk0 : kJ0.coeff (0 : ℤ) = kJ.coeff (0 : ℤ) - 744 := by
    simp [kJ0, kJ]
  have hkJ : kJ.coeff (0 : ℤ) = Aps.coeff 1 := by
    -- `0 = (1 : ℤ) + (-1)`.
    simpa using (coeff_kJ_shift (n := 1))
  -- Rearrange in `ℂ`.
  have hsub : kJ.coeff (0 : ℤ) - (744 : ℂ) = 0 := by
    -- `kJ0.coeff 0 = kJ.coeff 0 - 744` and `kJ0.coeff 0 = 0`.
    simpa [hk0] using hk'
  have : Aps.coeff 1 - (744 : ℂ) = 0 := by simpa [hkJ] using hsub
  exact sub_eq_zero.mp this

private lemma coeff_Aps_2 : Aps.coeff 2 = (firstJCoeff : ℂ) := by
  have hk :
      (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff (1 : ℤ) = (firstJCoeff : ℂ) := by
    simpa [coeff_J_q_1] using (kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q).2.2.1
  have hk0 : kJ0.coeff (1 : ℤ) = (firstJCoeff : ℂ) := by
    simpa [kJ0_eq_kleinJ0] using hk
  have hkshift : kJ0.coeff (1 : ℤ) = kJ.coeff (1 : ℤ) := by
    simp [kJ0, kJ]
  have hkJ : kJ.coeff (1 : ℤ) = Aps.coeff 2 := by
    -- `1 = (2 : ℤ) + (-1)`.
    simpa using (coeff_kJ_shift (n := 2))
  exact (hkJ.symm.trans (hkshift.symm.trans hk0))

private lemma coeff_Aps_3 : Aps.coeff 3 = (secondJCoeff : ℂ) := by
  have hk :
      (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff (2 : ℤ) = (secondJCoeff : ℂ) := by
    simpa [coeff_J_q_2] using (kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q).2.2.2
  have hk0 : kJ0.coeff (2 : ℤ) = (secondJCoeff : ℂ) := by
    simpa [kJ0_eq_kleinJ0] using hk
  have hkshift : kJ0.coeff (2 : ℤ) = kJ.coeff (2 : ℤ) := by
    simp [kJ0, kJ]
  have hkJ : kJ.coeff (2 : ℤ) = Aps.coeff 3 := by
    -- `2 = (3 : ℤ) + (-1)`.
    simpa using (coeff_kJ_shift (n := 3))
  exact (hkJ.symm.trans (hkshift.symm.trans hk0))

/-- Tail series of the `A(q)` power series after dropping the first 4 coefficients. -/
noncomputable def kleinA_tail_eval (q : ℂ) : ℂ :=
  ∑' n : ℕ, (Aps.coeff (n + 4)) * q ^ n

lemma eventually_kleinJ₀_qLaurent_eval_eq_trunc :
    ∀ᶠ q in 𝓝 (0 : ℂ), q ≠ 0 →
      kleinJ₀_qLaurent_eval q =
        q⁻¹ + (firstJCoeff : ℂ) * q + (secondJCoeff : ℂ) * q ^ 2 + q ^ 3 * kleinA_tail_eval q := by
  -- Work on a neighborhood where the defining `tsum` is absolutely summable.
  refine eventually_summable_norm_psTerm_kleinASeries.mono (fun q hsNorm0 hq0 => ?_)
  classical
  have hsNorm : Summable (fun n : ℕ => ‖psTerm Aps q n‖) := by
    simpa [Aps] using hsNorm0
  let f : ℕ → ℂ := fun n => psTerm Aps q n
  have hs : Summable f := hsNorm.of_norm
  have hs_tail : Summable (fun n : ℕ => f (n + 4)) :=
    hs.comp_injective (add_left_injective 4)
  have hq4_ne : (q ^ 4 : ℂ) ≠ 0 := pow_ne_zero 4 hq0
  -- Define `g n = Aps.coeff (n+4) * q^n`, so that `f (n+4) = q^4 * g n`.
  let g : ℕ → ℂ := fun n => (Aps.coeff (n + 4)) * q ^ n
  have hs_g : Summable g := by
    -- Show `g n = (q^4)⁻¹ * f (n+4)` (using `q ≠ 0`), then inherit summability.
    have hcongr : ∀ n : ℕ, (q ^ 4)⁻¹ * f (n + 4) = g n := by
      intro n
      dsimp [f, g, psTerm]
      -- Expand `q^(n+4)` and cancel the `q^4` factor.
      have hpow : q ^ (n + 4) = q ^ n * q ^ 4 := by
        simp [pow_add]
      -- Now compute in a commutative ring.
      calc
        (q ^ 4)⁻¹ * (Aps.coeff (n + 4) * q ^ (n + 4))
            = (q ^ 4)⁻¹ * (Aps.coeff (n + 4) * (q ^ n * q ^ 4)) := by simp [hpow]
        _ = (q ^ 4)⁻¹ * (Aps.coeff (n + 4) * q ^ n * q ^ 4) := by simp [mul_assoc]
        _ = (Aps.coeff (n + 4) * q ^ n) * ((q ^ 4)⁻¹ * q ^ 4) := by
              -- Reassociate and commute the scalar factor to expose `inv_mul_cancel`.
              ring_nf
        _ = Aps.coeff (n + 4) * q ^ n := by
              simp [hq4_ne]
    have hs_scaled : Summable (fun n : ℕ => (q ^ 4)⁻¹ * f (n + 4)) :=
      hs_tail.mul_left ((q ^ 4)⁻¹)
    -- Transport summability along pointwise equality.
    exact hs_scaled.congr hcongr
  have htail_tsum :
      (∑' n : ℕ, f (n + 4)) = q ^ 4 * (∑' n : ℕ, g n) := by
    calc
      (∑' n : ℕ, f (n + 4)) = ∑' n : ℕ, (q ^ 4) * g n := by
        refine tsum_congr (fun n => ?_)
        dsimp [f, g, psTerm]
        simp [pow_add, mul_assoc, mul_left_comm, mul_comm]
      _ = q ^ 4 * (∑' n : ℕ, g n) := by
        simpa using (hs_g.tsum_mul_left (q ^ 4))
  have hsplit :
      (∑' n : ℕ, f n) = (∑ n ∈ Finset.range 4, f n) + (∑' n : ℕ, f (n + 4)) := by
    simpa using (hs.sum_add_tsum_nat_add 4).symm
  have hsum4 :
      (∑ n ∈ Finset.range 4, f n) =
        (Aps.coeff 0)
          + (Aps.coeff 1) * q
          + (Aps.coeff 2) * q ^ 2
          + (Aps.coeff 3) * q ^ 3 := by
    -- Expand `range 4 = {0,1,2,3}` explicitly.
    have hsum :
        (∑ n ∈ Finset.range 4, f n) = f 0 + f 1 + f 2 + f 3 := by
      simp [Finset.sum_range_succ, add_assoc]
    -- Unfold `f` to `psTerm` and normalize `q^0`/`q^1`.
    -- This proof is purely finite, so `simp` is safe and fast here.
    rw [hsum]
    simp [f, psTerm, pow_two, pow_three, add_assoc, mul_assoc, mul_comm]
  -- Assemble the `tsum` defining `kleinJ₀_qLaurent_eval`.
  have htsum :
      (∑' n : ℕ, psTerm Aps q n) =
        (Aps.coeff 0)
          + (Aps.coeff 1) * q
          + (Aps.coeff 2) * q ^ 2
          + (Aps.coeff 3) * q ^ 3
          + q ^ 4 * (∑' n : ℕ, g n) := by
    calc
      (∑' n : ℕ, psTerm Aps q n) = (∑' n : ℕ, f n) := by
        simp [f]
      _ = (∑ n ∈ Finset.range 4, f n) + (∑' n : ℕ, f (n + 4)) := hsplit
      _ = ((Aps.coeff 0)
            + (Aps.coeff 1) * q
            + (Aps.coeff 2) * q ^ 2
            + (Aps.coeff 3) * q ^ 3) + q ^ 4 * (∑' n : ℕ, g n) := by
          rw [hsum4, htail_tsum]
      _ = (Aps.coeff 0)
            + (Aps.coeff 1) * q
            + (Aps.coeff 2) * q ^ 2
            + (Aps.coeff 3) * q ^ 3
            + q ^ 4 * (∑' n : ℕ, g n) := by ring
  -- Finally, substitute coefficients and simplify by canceling a factor of `q`.
  -- Let `S(q) := ∑ psTerm (kleinASeries ...) q n` and `T(q) := kleinA_tail_eval q`.
  have hS :
      (∑' n : ℕ, psTerm Aps q n) =
        (1 : ℂ) + (744 : ℂ) * q + (firstJCoeff : ℂ) * q ^ 2 + (secondJCoeff : ℂ) * q ^ 3
          + q ^ 4 * kleinA_tail_eval q := by
    -- Replace coefficients and rewrite `∑ g n` as `kleinA_tail_eval q`.
    have : (∑' n : ℕ, g n) = kleinA_tail_eval q := by rfl
    -- Start from `htsum` and normalize.
    simpa [this, coeff_Aps_0, coeff_Aps_1, coeff_Aps_2, coeff_Aps_3, mul_assoc,
      add_assoc, add_left_comm, add_comm] using htsum
  -- Prove the desired identity by multiplying through by `q` and canceling (using `hq0`).
  apply mul_left_cancel₀ hq0
  -- After multiplying by `q`, the goal becomes a polynomial identity; use `hS`.
  dsimp [kleinJ₀_qLaurent_eval, kleinJ_qLaurent_eval]
  -- Rewrite the cusp sum to the `Aps` abbreviation so we can apply `hS`.
  have hAps : kleinASeries (qExpansion₁ E4) (qExpansion₁ E6) = Aps := (show Aps = _ from rfl).symm
  rw [hAps]
  rw [hS]
  -- Normalize `q * (q⁻¹ * ·)` and rewrite powers.
  -- Reduce to a ring identity after canceling `q` using `hq0`.
  simp [mul_add, sub_eq_add_neg, mul_assoc, mul_comm, hq0, pow_succ]
  ring

lemma eventually_kleinJ₀_cusp_eq_trunc :
    ∀ᶠ q in 𝓝 (0 : ℂ), q ≠ 0 →
      kleinJ₀_cusp q =
        q⁻¹ + (firstJCoeff : ℂ) * q + (secondJCoeff : ℂ) * q ^ 2 + q ^ 3 * kleinA_tail_eval q := by
  filter_upwards [eventually_kleinJ₀_cusp_eq_kleinJ₀_qLaurent_eval,
    eventually_kleinJ₀_qLaurent_eval_eq_trunc] with q h1 h2 hq0
  exact (h1 hq0).trans (h2 hq0)

lemma exists_im_bound_kleinJ₀_eq_trunc :
    ∃ A : ℝ, ∀ τ : UpperHalfPlane, A < τ.im →
      kleinJ₀ τ =
        (q τ)⁻¹ + (firstJCoeff : ℂ) * (q τ)
          + (secondJCoeff : ℂ) * (q τ) ^ 2 + (q τ) ^ 3 * kleinA_tail_eval (q τ) := by
  -- Extract an explicit ball from `eventually_kleinJ₀_cusp_eq_trunc`.
  rcases (Metric.eventually_nhds_iff_ball).1 eventually_kleinJ₀_cusp_eq_trunc with ⟨ε, hεpos, hε⟩
  -- Choose an imaginary-part bound forcing `‖q τ‖ < ε`.
  rcases exists_im_bound_norm_q_lt ε hεpos with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  intro τ hIm
  have hq0 : q τ ≠ 0 := q_ne_zero τ
  have hball : q τ ∈ Metric.ball (0 : ℂ) ε := by
    have : ‖q τ‖ < ε := hA τ hIm
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using this
  have hcusp :
      kleinJ₀_cusp (q τ) =
        (q τ)⁻¹ + (firstJCoeff : ℂ) * (q τ)
          + (secondJCoeff : ℂ) * (q τ) ^ 2 + (q τ) ^ 3 * kleinA_tail_eval (q τ) :=
    (hε (q τ) hball) hq0
  -- Transfer from `τ` to cusp coordinate.
  simpa [q] using (kleinJ₀_eq_kleinJ₀_cusp (τ := τ)).trans hcusp

end HeytingLean.Moonshine.Modular
