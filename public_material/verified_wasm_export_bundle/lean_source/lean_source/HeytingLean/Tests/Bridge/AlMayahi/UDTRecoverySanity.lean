import HeytingLean.Bridge.AlMayahi.UDTRecovery

/-!
# Bridge.AlMayahi.UDTRecovery — Sanity Tests
-/

namespace HeytingLean.Tests.Bridge.AlMayahi.UDTRecoverySanity

open HeytingLean.Bridge.AlMayahi.UDTRecovery
open HeytingLean.Bridge.AlMayahi.UDTSynthesis

def sampleConstants : RecoveryConstants where
  c := 2
  h := 3
  G := 5
  c_pos := by norm_num
  h_pos := by norm_num
  G_pos := by norm_num

def sampleClock : ClockRateField where
  χ := fun _ => 1
  χ_pos := by intro _; norm_num
  χ_flat := by norm_num

def sampleGravity : GravityModel where
  constants := sampleConstants
  clock := sampleClock
  K := 4
  K_nonneg := by norm_num
  clock_sub_luminal := by
    intro _ _
    norm_num [sampleClock, sampleConstants]

def samplePotential : TauFieldPotential where
  V := fun τ => τ ^ 2
  τ₀ := 0
  V_has_minimum := by
    intro τ
    simp
    exact sq_nonneg τ

def sampleVariational : TauVariationalModel where
  potential := samplePotential
  dV := fun _ => 0
  sourceCoupling := 2

def sampleState : TauFieldState where
  τ := 1
  dtau := 0
  waveOp := 2
  laplace := 2
  source := ⟨1, by norm_num⟩

def sampleWave : TauWavefunction 1 where
  amp := fun _ => 2
  phase := fun _ => 0

example (s : ContinuousPhaseState) :
    synchronized s ↔ phaseDifference s = 0 := by
  rfl

example : clockPhase 0 3 = 0 :=
  clockPhase_zero_left

example : SatisfiesStaticPoisson sampleVariational sampleState := by
  apply static_poisson_source_form
  · rfl
  · rfl
  · apply euler_lagrange_of_balance
    norm_num [sampleState, sampleVariational]

example : causalVelocity sampleGravity 3 ≤ sampleConstants.c := by
  exact causalVelocity_le_c_of_clock_bound sampleGravity (by norm_num)

example : inverseSquareAcceleration sampleGravity (2 * 3) = inverseSquareAcceleration sampleGravity 3 / 4 := by
  simpa using newtonian_limit_of_inverse_square sampleGravity (r := 3) (by norm_num : (3 : ℝ) ≠ 0)

example : tauChargeContinuityResidual
    { E := fun _ => 0
      B := fun _ => 0
      J := fun _ => 0
      dtE := fun _ => 0
      dtB := fun _ => 0
      rho := ⟨1, by norm_num⟩
      divE := 1
      divB := 0
      divJ := -2
      dtRho := 2
      curlE := fun _ => 0
      curlB := fun _ => 0 } = 0 := by
  exact tau_continuity_equation_of_ampere_balance _ rfl

example : tauEnergy sampleConstants 3 = 1 := by
  norm_num [tauEnergy, sampleConstants]

example : restEnergyOfGap sampleConstants ⟨3, by norm_num⟩ = tauEnergy sampleConstants 3 := by
  exact rest_energy_of_asymmetry_gap sampleConstants ⟨3, by norm_num⟩ (by norm_num)

example : waveNormSq sampleWave = 4 := by
  norm_num [waveNormSq, HeytingLean.Eigen.sqSum, sampleWave]

example : (∑ i, bornWeight sampleWave i) = 1 := by
  apply born_normalization_surface
  norm_num [waveNormSq, HeytingLean.Eigen.sqSum, sampleWave]

/-- Born normalization with 3 components to exercise the Finset sum. -/
def sampleWave3 : TauWavefunction 3 where
  amp := fun i => [1, 2, 3].get (i.cast (by norm_num))
  phase := fun _ => 0

example : waveNormSq sampleWave3 = 14 := by
  norm_num [waveNormSq, HeytingLean.Eigen.sqSum, sampleWave3, Fin.sum_univ_three]

example : (∑ i, bornWeight sampleWave3 i) = 1 := by
  apply born_normalization_surface
  norm_num [waveNormSq, HeytingLean.Eigen.sqSum, sampleWave3, Fin.sum_univ_three]

example : standardRecoveries.eulerLagrange = .structuralProxy :=
  euler_lagrange_status

example : standardRecoveries.bell = .open :=
  bell_status

example : standardRecoveries.primeStability = .derived :=
  prime_stability_status

example : standardRecoveries.bornHeytingGap = .structuralProxy :=
  born_heyting_gap_status

example : standardRecoveries.koideFormula = .parameterizedRecovery :=
  koide_formula_status

end HeytingLean.Tests.Bridge.AlMayahi.UDTRecoverySanity
