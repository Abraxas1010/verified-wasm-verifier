import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Beta Function and Dimensional Flow

Formalizes the dimensional flow ODE dD_eff/dμ = β(D_eff) from
Veselov's "Fractal Universe" paper (Section 4.1, Equation 3).
The beta function has leading order β(D) = A(4 - D) with A > 0,
giving D* = 4 as a stable IR fixed point.
-/

namespace HeytingLean.FractalUniverse.DimensionalFlow

/-- The dimensional flow ODE: dD_eff/dμ = β(D_eff).
    Leading order: β(D) = A(4 - D) + O((4-D)²).
    Source: Veselov Eq. (3). -/
structure DimFlowData where
  /-- Effective dimension as function of energy scale μ. -/
  D_eff : ℝ → ℝ
  /-- Beta function. -/
  β : ℝ → ℝ
  /-- The flow equation holds. -/
  is_flow : ∀ μ, HasDerivAt D_eff (β (D_eff μ)) μ
  /-- Leading-order coefficient A > 0. -/
  A : ℝ
  A_pos : 0 < A
  /-- Higher-order correction bound constant. -/
  C_ho : ℝ
  C_ho_nonneg : 0 ≤ C_ho
  /-- Leading-order approximation with error bound. -/
  beta_leading : ∀ D, |β D - A * (4 - D)| ≤ C_ho * (4 - D) ^ 2

/-- β(4) = 0 — D* = 4 is a fixed point of the beta function.
    At D = 4 the leading term vanishes and the error bound gives |β 4| ≤ 0. -/
theorem beta_zero_at_four (flow : DimFlowData) : flow.β 4 = 0 := by
  have h := flow.beta_leading 4
  simp only [sub_self, mul_zero, sq] at h
  -- h : |flow.β 4 - 0| ≤ 0
  rw [sub_zero] at h
  exact abs_nonpos_iff.mp h

/-- The linearized ODE dD/dμ = A(4-D) has explicit solution
    D(μ) = 4 - (4 - D₀) · exp(-A · μ).
    Verified by direct differentiation. -/
theorem explicit_linearized_solution (A D₀ μ : ℝ) (_hA : 0 < A) :
    HasDerivAt (fun μ => 4 - (4 - D₀) * Real.exp (-A * μ))
      (A * (4 - (4 - (4 - D₀) * Real.exp (-A * μ)))) μ := by
  have h1 : HasDerivAt (fun μ => -A * μ) (-A * 1) μ :=
    (hasDerivAt_id μ).const_mul (-A)
  simp only [mul_one] at h1
  have h2 : HasDerivAt (fun μ => Real.exp (-A * μ)) (Real.exp (-A * μ) * (-A)) μ :=
    h1.exp
  have h3 : HasDerivAt (fun μ => (4 - D₀) * Real.exp (-A * μ))
      ((4 - D₀) * (Real.exp (-A * μ) * (-A))) μ :=
    h2.const_mul (4 - D₀)
  have h4 : HasDerivAt (fun μ => 4 - (4 - D₀) * Real.exp (-A * μ))
      (0 - (4 - D₀) * (Real.exp (-A * μ) * (-A))) μ :=
    (hasDerivAt_const μ 4).sub h3
  convert h4 using 1
  ring

end HeytingLean.FractalUniverse.DimensionalFlow
