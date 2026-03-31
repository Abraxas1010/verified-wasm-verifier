import Mathlib
import HeytingLean.Analysis.PMBoundedControl

namespace HeytingLean
namespace Tests
namespace Analysis

open HeytingLean.Analysis.PMBoundedControl

example : |SatRational 2 10| ≤ 2 := by
  norm_num [SatRational]

example : Monotone (SatRational 3) := by
  exact sat_rational_monotone (by norm_num)

example : SatRational 4 (-3) = -SatRational 4 3 := by
  simpa using sat_rational_odd (Q_PM := 4) (x := 3)

example : 0 ≤ TokamakRisk 2 1 3 := by
  exact tokamak_risk_nonneg (by norm_num) (by norm_num) (by norm_num)

example : 1 ≤ progressionDensity 1 4 1 := by
  exact progression_density_ge_one (by norm_num) (by norm_num) (by norm_num)

example : effectiveStep 3 6 ≤ (1 : ℝ) := by
  have h : 3 / (1 : ℝ) ≤ (6 : ℝ) := by norm_num
  simpa [effectiveStep] using effective_step_vanishes_of_large_density
    (Δσ := 3) (ρ := 6) (ε := 1) (by norm_num) (by norm_num) (by norm_num) h

example : gateWeight 2 10 1 = 0 := by
  norm_num [gateWeight, clamp01]

example : blendedUpdate (gateWeight 11 10 1) 3 7 = 7 := by
  have h : (10 : ℝ) ≤ 11 := by norm_num
  simpa using blended_completed_when_critical (Q := 11) (Q_PM := 10) (ε := 1)
    (classical := 3) (completed := 7) (by norm_num) h

example : euclideanNorm (SatNormBounded 2 (fun _ : Fin 2 => (3 : ℝ))) ≤ 2 := by
  exact sat_norm_bounded_le (n := 2) (by norm_num) _

example :
    Eigen.sqSum (ComponentwiseCompletion 2 (fun _ : Fin 3 => (5 : ℝ))) ≤ 3 * 2^2 := by
  simpa using componentwise_sqSum_le (n := 3) 2 (by norm_num) (fun _ : Fin 3 => (5 : ℝ))

example : euclideanNorm (fun _ : Fin 3 => (2 : ℝ)) ≤ Real.sqrt 3 * 2 := by
  exact componentwise_implies_norm (n := 3) 2 (by norm_num) _ (fun _ => by norm_num)

end Analysis
end Tests
end HeytingLean
