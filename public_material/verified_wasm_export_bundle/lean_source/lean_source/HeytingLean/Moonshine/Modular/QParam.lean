import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

set_option autoImplicit false

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane Function
open Filter

local notation "𝕢" => Periodic.qParam

/-- The standard `q`-parameter `q = exp(2 * pi * I * τ)` for `τ ∈ ℍ`. -/
noncomputable def q (τ : ℍ) : ℂ :=
  𝕢 1 τ

lemma norm_q_lt_one (τ : ℍ) : ‖q τ‖ < 1 := by
  simpa [q] using UpperHalfPlane.norm_qParam_lt_one (n := 1) τ

lemma q_ne_zero (τ : ℍ) : q τ ≠ 0 := by
  simp [q, Function.Periodic.qParam, Complex.exp_ne_zero]

lemma tendsto_q_atImInfty :
    Tendsto q UpperHalfPlane.atImInfty (nhdsWithin (0 : ℂ) ({0}ᶜ)) := by
  simpa [q] using
    (Function.Periodic.qParam_tendsto (h := (1 : ℝ)) (by norm_num)).comp
      UpperHalfPlane.tendsto_coe_atImInfty

lemma exists_im_bound_norm_q_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ τ : ℍ, A < τ.im → ‖q τ‖ < ε := by
  -- A sufficient bound: force `‖q τ‖ < exp(-2πA)` via `norm_qParam_lt_iff`, and then choose
  -- `A` so that `exp(-2πA) = ε * exp(-2π) < ε`.
  let A : ℝ := (-Real.log ε) / (2 * Real.pi) + 1
  refine ⟨A, ?_⟩
  intro τ hAτ
  have hnorm_lt_exp : ‖q τ‖ < Real.exp (-2 * Real.pi * A) := by
    have h :=
      (Function.Periodic.norm_qParam_lt_iff (h := (1 : ℝ)) (hh := by norm_num)
        (A := A) (z := (τ : ℂ))).2 (by simpa using hAτ)
    simpa [q, Function.Periodic.qParam, div_one] using h
  have hexp_lt : Real.exp (-2 * Real.pi * A) < ε := by
    have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
      exact ne_of_gt this
    have hfactor : Real.exp (-2 * Real.pi * A) = ε * Real.exp (-2 * Real.pi) := by
      have hc : -(2 * Real.pi * (-Real.log ε / (2 * Real.pi))) = Real.log ε := by
        -- `-(2π * (-log ε / (2π))) = log ε`
        have hcancel :
            (2 * Real.pi : ℝ) * (-Real.log ε) / (2 * Real.pi) = -Real.log ε := by
          simpa [mul_assoc] using (mul_div_cancel_left₀ (-Real.log ε) h2pi_ne)
        have hmul :
            (2 * Real.pi : ℝ) * (-Real.log ε) / (2 * Real.pi)
              = (2 * Real.pi : ℝ) * (-Real.log ε / (2 * Real.pi)) := by
          -- `a*b/c = a*(b/c)`
          simpa [mul_assoc] using
            (mul_div_assoc (2 * Real.pi : ℝ) (-Real.log ε) (2 * Real.pi))
        calc
          -(2 * Real.pi * (-Real.log ε / (2 * Real.pi)))
              = -((2 * Real.pi : ℝ) * (-Real.log ε) / (2 * Real.pi)) := by
                  simpa using congrArg Neg.neg hmul.symm
          _ = -(-Real.log ε) := by rw [hcancel]
          _ = Real.log ε := by simp
      have hdecomp : -(2 * Real.pi * A) = Real.log ε + -(2 * Real.pi) := by
        -- Expand `A := (-log ε)/(2π) + 1` and use `hc`.
        dsimp [A]
        calc
          -(2 * Real.pi * ((-Real.log ε) / (2 * Real.pi) + 1))
              = -(2 * Real.pi * ((-Real.log ε) / (2 * Real.pi))) + -(2 * Real.pi * 1) := by
                  ring
          _ = Real.log ε + -(2 * Real.pi) := by
                simp [hc]
      calc
        Real.exp (-2 * Real.pi * A)
            = Real.exp (-(2 * Real.pi * A)) := by ring_nf
        _ = Real.exp (Real.log ε + -(2 * Real.pi)) := by
              simp [hdecomp]
        _ = Real.exp (Real.log ε) * Real.exp (-(2 * Real.pi)) := by
              simp [Real.exp_add, mul_comm]
        _ = ε * Real.exp (-2 * Real.pi) := by
              simp [Real.exp_log hε]
    have hlt1 : Real.exp (-2 * Real.pi) < 1 := by
      have hneg : (-2 * Real.pi : ℝ) < 0 := by nlinarith [Real.pi_pos]
      simpa [Real.exp_lt_one_iff] using hneg
    calc
      Real.exp (-2 * Real.pi * A) = ε * Real.exp (-2 * Real.pi) := hfactor
      _ < ε * 1 := (mul_lt_mul_of_pos_left hlt1 hε)
      _ = ε := by simp
  exact lt_trans hnorm_lt_exp hexp_lt

end HeytingLean.Moonshine.Modular
