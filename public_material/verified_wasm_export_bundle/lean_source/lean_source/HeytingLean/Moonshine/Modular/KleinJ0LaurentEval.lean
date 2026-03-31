import HeytingLean.Moonshine.Modular.KleinCuspLaurentBridge
import HeytingLean.Moonshine.Modular.QParam

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open scoped BigOperators
open scoped Topology
open Filter

/-!
## Evaluating the formal `kleinJ₀_qLaurent` near `q = 0`

Mathlib does not provide an `eval` of `HahnSeries ℤ ℂ` as an analytic function on `ℂ`.
For Moonshine we only need the special Laurent series
`kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)`, which is `q⁻¹` times a power series
minus a constant. We define its evaluation on the punctured unit disk via the power-series `tsum`.

This is the final "analytic = formal" bridge we use for downstream coefficient comparisons.
-/

/-- Evaluate the formal Laurent series for `kleinJ` at a complex `q` via the power-series `tsum`. -/
noncomputable def kleinJ_qLaurent_eval (q : ℂ) : ℂ :=
  q⁻¹ * (∑' n : ℕ, psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n)

/-- Evaluate the formal Laurent series for `kleinJ₀ = kleinJ - 744` at a complex `q`. -/
noncomputable def kleinJ₀_qLaurent_eval (q : ℂ) : ℂ :=
  kleinJ_qLaurent_eval q - 744

lemma eventually_kleinJ₀_cusp_eq_kleinJ₀_qLaurent_eval :
    ∀ᶠ q in 𝓝 (0 : ℂ), q ≠ 0 → kleinJ₀_cusp q = kleinJ₀_qLaurent_eval q := by
  refine (eventually_kleinJ₀_cusp_eq_qInv_tsum_kleinASeries).mono (fun q h => ?_)
  intro hq0
  -- `kleinJ₀_qLaurent_eval` is definitionally the RHS.
  simpa [kleinJ₀_qLaurent_eval, kleinJ_qLaurent_eval, mul_assoc] using h hq0

lemma exists_ball_kleinJ₀_cusp_eq_kleinJ₀_qLaurent_eval :
    ∃ ε > (0 : ℝ), ∀ q : ℂ, q ∈ Metric.ball (0 : ℂ) ε → q ≠ 0 →
      kleinJ₀_cusp q = kleinJ₀_qLaurent_eval q := by
  -- Unpack the neighborhood statement into an explicit ball.
  rcases (Metric.eventually_nhds_iff_ball).1 eventually_kleinJ₀_cusp_eq_kleinJ₀_qLaurent_eval with
    ⟨ε, hεpos, hε⟩
  refine ⟨ε, hεpos, ?_⟩
  intro q hq hq0
  exact (hε q hq) hq0

lemma exists_im_bound_kleinJ₀_eq_kleinJ₀_qLaurent_eval :
    ∃ A : ℝ, ∀ τ : UpperHalfPlane, A < τ.im → kleinJ₀ τ = kleinJ₀_qLaurent_eval (q τ) := by
  rcases exists_ball_kleinJ₀_cusp_eq_kleinJ₀_qLaurent_eval with ⟨ε, hεpos, hε⟩
  -- Choose an explicit imaginary-part bound forcing `‖q τ‖ < ε`.
  let A : ℝ := (-Real.log ε) / (2 * Real.pi) + 1
  refine ⟨A, ?_⟩
  intro τ hAτ
  have hq_ne : q τ ≠ 0 := by
    simp [q, Function.Periodic.qParam, Complex.exp_ne_zero]
  have hnorm_lt_exp : ‖q τ‖ < Real.exp (-2 * Real.pi * A) := by
    -- Convert the condition on `τ.im` using `norm_qParam_lt_iff`.
    have h :=
      (Function.Periodic.norm_qParam_lt_iff (h := (1 : ℝ)) (hh := by norm_num)
        (A := A) (z := (τ : ℂ))).2 ?_
    · simpa [q, Function.Periodic.qParam, div_one] using h
    · simpa using hAτ
  have hexp_lt : Real.exp (-2 * Real.pi * A) < ε := by
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
    have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2pi_pos
    have hfactor :
        Real.exp (-2 * Real.pi * A) = ε * Real.exp (-2 * Real.pi) := by
      calc
        Real.exp (-2 * Real.pi * A)
            = Real.exp ((-2 * Real.pi : ℝ) * A) := by simp [mul_assoc]
        _ = ε * Real.exp (-2 * Real.pi) := by
          -- Use `exp_add` at the level of `(-2π) * A`, then simplify the first factor to `ε`.
          let c : ℝ := (-2 * Real.pi : ℝ)
          have hc : c * ((-Real.log ε) / (2 * Real.pi)) = Real.log ε := by
            -- Cancel `2π` and the two negations.
            calc
              c * ((-Real.log ε) / (2 * Real.pi))
                  = (c * (-Real.log ε)) / (2 * Real.pi) := by
                      -- `a * (b / d) = (a * b) / d`.
                      simpa [mul_assoc] using
                        (mul_div_assoc c (-Real.log ε) (2 * Real.pi)).symm
              _ = ((2 * Real.pi : ℝ) * Real.log ε) / (2 * Real.pi) := by
                    simp [c, mul_assoc, mul_comm]
              _ = Real.log ε := by
                    simpa [mul_assoc] using (mul_div_cancel_left₀ (Real.log ε) h2pi_ne)
          have hdecomp : c * A = c * ((-Real.log ε) / (2 * Real.pi)) + c := by
            simp [A, c, mul_add, mul_assoc]
          calc
            Real.exp ((-2 * Real.pi : ℝ) * A)
                = Real.exp (c * A) := by simp [c]
            _ = Real.exp (c * ((-Real.log ε) / (2 * Real.pi)) + c) := by
                  simp [hdecomp]
            _ = Real.exp (c * ((-Real.log ε) / (2 * Real.pi))) * Real.exp c := by
                  simp [Real.exp_add]
            _ = Real.exp (Real.log ε) * Real.exp c := by
                  simp [hc]
            _ = ε * Real.exp c := by
                  simp [Real.exp_log hεpos]
            _ = ε * Real.exp (-2 * Real.pi) := by
                  simp [c]
    have hlt1 : Real.exp (-2 * Real.pi) < 1 := by
      have hneg : (-2 * Real.pi : ℝ) < 0 := by nlinarith [Real.pi_pos]
      simpa [Real.exp_lt_one_iff] using hneg
    calc
      Real.exp (-2 * Real.pi * A) = ε * Real.exp (-2 * Real.pi) := hfactor
      _ < ε * 1 := (mul_lt_mul_of_pos_left hlt1 hεpos)
      _ = ε := by simp
  have hnorm : ‖q τ‖ < ε := lt_trans hnorm_lt_exp hexp_lt
  have hq_ball : q τ ∈ Metric.ball (0 : ℂ) ε := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hnorm
  have hcusp : kleinJ₀_cusp (q τ) = kleinJ₀_qLaurent_eval (q τ) :=
    hε (q τ) hq_ball hq_ne
  -- Transfer from `τ` to the cusp coordinate.
  simpa [q] using (kleinJ₀_eq_kleinJ₀_cusp (τ := τ)).trans hcusp

end HeytingLean.Moonshine.Modular
