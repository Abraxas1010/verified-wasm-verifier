import HeytingLean.Bridge.Sharma.AetherGovernorConvergence

namespace HeytingLean.Tests.Bridge.Sharma

open HeytingLean.Bridge.Sharma.AetherGovernor
open HeytingLean.Bridge.Sharma.AetherGovernorConvergence

#check candidateRho
#check validatorRegime
#check validateTargetRho
#check contractionRho
#check govStep_sets_ePrev_to_error
#check lyapunov_strict_descent
#check geometric_convergence_of_stepwise_contraction
#check candidateRho_mem_Ioo_of_validatorRegime
#check candidateRho_lt_contractionRho_counterexample
#check lyapunov_rises_on_second_pd_step_counterexample

private noncomputable def demoParams : GovParams where
  alpha := (1 : Real) / 100
  beta := (1 : Real) / 20
  epsMin := (1 : Real) / 10
  epsMax := 10
  target := 5
  hAlpha := by norm_num
  hBeta := by norm_num
  hEps := by norm_num
  hEpsMinPos := by norm_num

example : candidateRho demoParams = (99 : Real) / 100 := by
  norm_num [candidateRho, demoParams]

example : validatorRegime demoParams 1 := by
  constructor
  · norm_num
  · norm_num [demoParams]

example : 0 < candidateRho demoParams ∧ candidateRho demoParams < 1 := by
  exact candidateRho_mem_Ioo_of_validatorRegime demoParams 1 (by
    constructor
    · norm_num
    · norm_num [demoParams])

example : validateParams demoParams 1 = true := by
  exact (validateParams_eq_true_iff demoParams 1).2 (by
    constructor
    · norm_num
    · norm_num [demoParams])

example : validateTargetRho demoParams 1 ((99 : Real) / 100) = true := by
  exact (validateTargetRho_eq_true_iff demoParams 1 ((99 : Real) / 100)).2 (by
    constructor
    · constructor
      · norm_num
      · norm_num [demoParams]
    · constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num [demoParams])

private noncomputable def demoState : GovState where
  eps := 1
  ePrev := 0

example : contractionRho demoParams demoState 2 1 = (35 : Real) / 41 := by
  norm_num [contractionRho, govError, demoParams, demoState]

example :
    0 ≤ contractionRho demoParams demoState 2 1 ∧
      contractionRho demoParams demoState 2 1 < 1 := by
  constructor
  · exact contractionRho_nonneg demoParams demoState 2 1 (by norm_num) (by norm_num)
      (by norm_num [demoState]) (by norm_num [demoParams, demoState])
  · exact contractionRho_lt_one demoParams demoState 2 1 (by norm_num) (by norm_num)
      (by norm_num [demoState]) (by norm_num [demoParams, demoState])

example :
    lyapunov (govError demoParams (govStep demoParams demoState 2 1) 2) <
      lyapunov (govError demoParams demoState 2) := by
  exact lyapunov_strict_descent demoParams demoState 2 1 (by norm_num) (by norm_num)
    (by norm_num [demoState])
    (by norm_num [govAdjustment, govError, demoParams, demoState])
    (by norm_num [govAdjustment, govError, demoParams, demoState])
    (by norm_num [demoState])
    (by norm_num [demoParams, demoState])
    (by norm_num [govError, demoParams, demoState])

/-- `govStep` destroys the `ePrev = 0` hypothesis after one nonzero-error step. -/
example : (govStep demoParams demoState 2 1).ePrev = govError demoParams demoState 2 := by
  simpa using govStep_sets_ePrev_to_error demoParams demoState 2 1

private noncomputable def strictErrors (n : Nat) : Real :=
  if n = 0 then
    3
  else
    ((35 : Real) / 41) ^ n * 2

example :
    ∀ n : Nat, |strictErrors n| ≤ ((35 : Real) / 41) ^ n * |strictErrors 0| := by
  apply geometric_convergence_of_stepwise_contraction (rho := (35 : Real) / 41)
  · norm_num
  · intro k
    cases k with
    | zero =>
        norm_num [strictErrors]
    | succ k =>
        have hr : 0 ≤ (35 : Real) / 41 := by norm_num
        have hpowk : 0 ≤ ((35 : Real) / 41) ^ k := by positivity
        simp [strictErrors, pow_succ, abs_mul, abs_of_nonneg, hr, hpowk, mul_left_comm, mul_comm]

example : |strictErrors 1| < ((35 : Real) / 41) ^ 1 * |strictErrors 0| := by
  norm_num [strictErrors]

example : validatorRegime candidateBridgeWitnessParams 1 := by
  exact validatorRegime_candidateBridgeWitness

example :
    candidateRho candidateBridgeWitnessParams <
      contractionRho candidateBridgeWitnessParams candidateBridgeWitnessState 100 1 := by
  exact candidateRho_lt_contractionRho_counterexample

example : validatorRegime pdCounterexampleParams 1 := by
  exact validatorRegime_pdCounterexample

example :
    lyapunov (govError pdCounterexampleParams pdCounterexampleState2 20) >
      lyapunov (govError pdCounterexampleParams pdCounterexampleState1 20) := by
  exact lyapunov_rises_on_second_pd_step_counterexample

end HeytingLean.Tests.Bridge.Sharma
