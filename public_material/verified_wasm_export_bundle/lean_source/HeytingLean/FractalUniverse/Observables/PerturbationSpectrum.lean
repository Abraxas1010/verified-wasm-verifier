import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Perturbation Spectrum Modification

Formalizes the fractal correction to the primordial power spectrum
from Veselov's "Fractal Universe" paper (Section 6.1.1, Equation 8).
Δn_s(k) = -(4 - D_s(k)) / k · ln(k / k_Planck)
-/

namespace HeytingLean.FractalUniverse.Observables

/-- The fractal correction to the spectral index.
    Source: Veselov Eq. (8). -/
noncomputable def fractalCorrection (D_s : ℝ → ℝ) (k_Planck k : ℝ) : ℝ :=
  -(4 - D_s k) / k * Real.log (k / k_Planck)

/-- When D_s = 4 everywhere, the fractal correction vanishes. -/
theorem no_correction_at_four (k_Planck k : ℝ) :
    fractalCorrection (fun _ => 4) k_Planck k = 0 := by
  unfold fractalCorrection
  simp [sub_self]

/-- The modified power spectrum.
    P_R(k) = A_s · (k/k_*)^(n_s - 1 + Δn_s(k))
    Source: Veselov Eq. (8). -/
noncomputable def fractalSpectrum (A_s k_star n_s : ℝ) (D_s : ℝ → ℝ) (k_Planck k : ℝ) : ℝ :=
  A_s * (k / k_star) ^ (n_s - 1 + fractalCorrection D_s k_Planck k)

/-- When D_s = 4, the modified spectrum equals the standard spectrum. -/
theorem spectrum_standard_at_four (A_s k_star n_s k_Planck k : ℝ) :
    fractalSpectrum A_s k_star n_s (fun _ => 4) k_Planck k
      = A_s * (k / k_star) ^ (n_s - 1) := by
  unfold fractalSpectrum
  rw [no_correction_at_four, add_zero]

end HeytingLean.FractalUniverse.Observables
