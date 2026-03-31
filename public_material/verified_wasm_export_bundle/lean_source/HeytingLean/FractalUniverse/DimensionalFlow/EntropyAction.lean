import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Entropy Action and Stability Potential

Formalizes the stability potential F(D_s) = (1/2)α(D_s - 4)² from
Veselov's "Fractal Universe" paper (Section 4.2, Equation 5).
The potential has a unique minimum at D_s = 4, corresponding to
the stable IR fixed point of the dimensional flow.
-/

namespace HeytingLean.FractalUniverse.DimensionalFlow

/-- Stability potential F(D_s) = (1/2) · α · (D_s - 4)².
    Source: Veselov Section 4.2, Eq. (5). -/
noncomputable def stabilityPotential (α : ℝ) (D_s : ℝ) : ℝ :=
  (1 / 2) * α * (D_s - 4) ^ 2

/-- The stability potential attains its minimum at D_s = 4. -/
theorem stability_minimum (α : ℝ) (hα : 0 < α) :
    ∀ D, stabilityPotential α 4 ≤ stabilityPotential α D := by
  intro D
  unfold stabilityPotential
  have h1 : (0 : ℝ) ≤ (D - 4) ^ 2 := sq_nonneg _
  nlinarith

/-- The minimum at D_s = 4 is strict for D ≠ 4. -/
theorem stability_minimum_strict (α : ℝ) (hα : 0 < α) :
    ∀ D, D ≠ 4 → stabilityPotential α 4 < stabilityPotential α D := by
  intro D hD
  unfold stabilityPotential
  have h1 : D - 4 ≠ 0 := sub_ne_zero.mpr hD
  have h2 : (0 : ℝ) < (D - 4) ^ 2 := by positivity
  nlinarith

/-- At the minimum, the potential value is zero. -/
theorem stability_at_minimum (α : ℝ) : stabilityPotential α 4 = 0 := by
  unfold stabilityPotential
  ring

end HeytingLean.FractalUniverse.DimensionalFlow
