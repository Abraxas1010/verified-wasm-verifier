import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
# Modified Gravitational Potential

Formalizes the fractal correction to the Newtonian gravitational potential
from Veselov's "Fractal Universe" paper (Section 6.3.2, Equation 13).
Φ(r) = -(GM/r)(1 + ε(ln(r/r₀) + γ_E - 3/2) + O(ε²))
-/

namespace HeytingLean.FractalUniverse.Observables

/-- Modified Newtonian potential with fractal correction.
    Source: Veselov Eq. (13). The Euler-Mascheroni constant is
    approximated here; the exact value is not needed for
    structural theorems. -/
noncomputable def fractalPotential (G_N M r r₀ ε γ_E : ℝ) : ℝ :=
  -(G_N * M / r) * (1 + ε * (Real.log (r / r₀) + γ_E - 3 / 2))

/-- At ε = 0 the potential reduces to the standard Newtonian form. -/
theorem newtonian_limit (G_N M r r₀ γ_E : ℝ) :
    fractalPotential G_N M r r₀ 0 γ_E = -(G_N * M / r) := by
  unfold fractalPotential; ring

/-- The fractal potential decomposes as Newtonian + ε · correction,
    exhibiting the perturbative structure explicitly. -/
theorem fractal_correction_linear (G_N M r r₀ γ_E ε : ℝ) :
    fractalPotential G_N M r r₀ ε γ_E =
    -(G_N * M / r) + ε * (-(G_N * M / r) * (Real.log (r / r₀) + γ_E - 3 / 2)) := by
  unfold fractalPotential; ring

end HeytingLean.FractalUniverse.Observables
