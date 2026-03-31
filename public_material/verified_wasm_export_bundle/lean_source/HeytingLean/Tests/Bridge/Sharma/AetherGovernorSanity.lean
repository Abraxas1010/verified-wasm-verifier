import HeytingLean.Bridge.Sharma.AetherGovernor

namespace HeytingLean.Tests.Bridge.Sharma

open HeytingLean.Bridge.Sharma.AetherGovernor

#check clamp
#check lyapunov
#check @lyapunov_descent
#check @govError_contraction_noclamp
#check @govError_contraction_equilibrium
#check @epsilon_bounded
#check gainStable
#check hft_gain_margin
#check hft_gain_margin_refined

example : clamp (5 : Real) 1 3 = 3 := by
  norm_num [clamp]

example : clamp (-2 : Real) 1 3 = 1 := by
  norm_num [clamp]

example : lyapunov (2 : Real) = 2 := by
  norm_num [lyapunov]

example : (0.01 : Real) + 0.05 / 1 < 1 := by
  simpa using hft_gain_margin_refined 1 (by norm_num)

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

private noncomputable def demoState : GovState where
  eps := 1
  ePrev := 0

-- Corrected-sign no-clamp step: eps' = 0.82 = 41/50.
example : (govStep demoParams demoState 2 1).eps = (41 : Real) / 50 := by
  norm_num [govStep, govAdjustment, govError, clamp, demoParams, demoState]

example : demoParams.epsMin ≤ demoState.eps + govAdjustment demoParams demoState 2 1 := by
  norm_num [govAdjustment, govError, demoParams, demoState]

example : demoState.eps + govAdjustment demoParams demoState 2 1 ≤ demoParams.epsMax := by
  norm_num [govAdjustment, govError, demoParams, demoState]

-- With corrected sign, contraction holds at the demo operating point.
example :
    |govError demoParams (govStep demoParams demoState 2 1) 2|
      < |govError demoParams demoState 2| := by
  norm_num [govError, govStep, govAdjustment, clamp, demoParams, demoState]

example : gainStable demoParams 2 1 := by
  norm_num [gainStable, demoParams]

private noncomputable def eqParams : GovParams where
  alpha := (1 : Real) / 10
  beta := 0
  epsMin := (1 : Real) / 10
  epsMax := 10
  target := 2
  hAlpha := by norm_num
  hBeta := by norm_num
  hEps := by norm_num
  hEpsMinPos := by norm_num

private noncomputable def eqState : GovState where
  eps := 1
  ePrev := 0

-- Regime test: at equilibrium, contraction holds (both sides are 0).
example :
    |govError eqParams (govStep eqParams eqState 2 1) 2|
      ≤ |govError eqParams eqState 2| := by
  have hNoClampLo : eqParams.epsMin ≤ eqState.eps + govAdjustment eqParams eqState 2 1 := by
    norm_num [govAdjustment, govError, eqParams, eqState]
  have hNoClampHi : eqState.eps + govAdjustment eqParams eqState 2 1 ≤ eqParams.epsMax := by
    norm_num [govAdjustment, govError, eqParams, eqState]
  have hErr : govError eqParams eqState 2 = 0 := by
    norm_num [govError, eqParams, eqState]
  exact govError_contraction_equilibrium eqParams eqState 2 1 (by norm_num) (by norm_num)
    hNoClampLo hNoClampHi hErr (by rfl)

end HeytingLean.Tests.Bridge.Sharma
