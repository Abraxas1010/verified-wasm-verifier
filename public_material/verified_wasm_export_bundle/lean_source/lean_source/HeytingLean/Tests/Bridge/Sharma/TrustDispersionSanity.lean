import HeytingLean.Bridge.Sharma.TrustStabilityBounds
import Lean.Data.Json

namespace HeytingLean.Tests.Bridge.Sharma

open HeytingLean.Bridge.Sharma.AetherGovernor
open HeytingLean.Bridge.Sharma.AetherGovernorConvergence
open HeytingLean.Bridge.Sharma.TrustDispersion
open HeytingLean.PDE.Madelung
open Lean

#check TrustBridgeAssumptions
#check TrustDensityField.physics
#check TrustOperatingPoint.exactContractionFactor
#check TrustOperatingPoint.lyapunov_descent
#check mkTrustDispersionCertificate
#check high_k_dominated_by_friction
#check crossoverWavenumber
#check mkStabilityBoundExport

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

private noncomputable def demoAssumptions : TrustBridgeAssumptions demoParams 1 where
  hDt := by norm_num
  hValidator := by
    constructor
    · norm_num
    · norm_num [demoParams]
  hBetaPos := by norm_num [demoParams]
  hTargetPos := by norm_num [demoParams]

private noncomputable def demoField : TrustDensityField where
  govParams := demoParams
  dt := 1
  assumptions := demoAssumptions

private noncomputable def demoState : GovState where
  eps := 1
  ePrev := 0

private noncomputable def demoOperatingPoint : TrustOperatingPoint demoField where
  state := demoState
  delta := 2
  hDelta := by norm_num
  hEpsPos := by norm_num [demoState]
  hStateLo := by norm_num [demoField, demoParams, demoState]
  hStateHi := by norm_num [demoField, demoParams, demoState]
  hNoClampLo := by
    norm_num [demoField, demoState, demoParams, govAdjustment, govError]
  hNoClampHi := by
    norm_num [demoField, demoState, demoParams, govAdjustment, govError]
  hPrev := by rfl
  hGammaTargetLeEps := by
    norm_num [demoField, demoParams, demoState]

private noncomputable def demoCert : TrustDispersionCertificate :=
  mkTrustDispersionCertificate demoField 4

example : demoField.proxyContraction = (99 : Real) / 100 := by
  norm_num [TrustDensityField.proxyContraction, candidateRho, demoField, demoParams]

example : demoField.physics.infoFriction = (1 : Real) / 40 := by
  norm_num [TrustDensityField.physics, govParamsToTrustPhysics, demoField, demoAssumptions, demoParams]

example : demoField.physics.trustElasticity ^ 2 = (1 : Real) / 100 := by
  simpa [demoField, demoParams] using demoField.trustElasticity_sq

example :
    dispersion_coefficient demoField.toEquilibriumState.consts =
      demoField.physics.infoFriction := by
  simpa [demoField] using demoField.dispersionCoefficient_eq_infoFriction

example :
    0 ≤ demoOperatingPoint.exactContractionFactor ∧
      demoOperatingPoint.exactContractionFactor < 1 := by
  exact demoOperatingPoint.exactContractionFactor_mem_Ioo

example : demoOperatingPoint.exactContractionFactor = (35 : Real) / 41 := by
  norm_num [TrustOperatingPoint.exactContractionFactor, contractionRho, govError,
    demoField, demoParams, demoState, demoOperatingPoint]

example :
    lyapunov (govError demoField.govParams
        (govStep demoField.govParams demoOperatingPoint.state demoOperatingPoint.delta demoField.dt)
        demoOperatingPoint.delta) ≤
      lyapunov (govError demoField.govParams demoOperatingPoint.state demoOperatingPoint.delta) := by
  exact demoOperatingPoint.lyapunov_descent

example : demoCert.governorRho = demoField.proxyContraction := by
  simpa [demoCert] using demoCert.governorRho_eq

example : demoCert.omegaSquared = (8 : Real) / 25 := by
  have hSq : demoField.physics.trustElasticity ^ 2 = (1 : Real) / 100 := by
    simpa [demoField, demoParams] using demoField.trustElasticity_sq
  have hD : demoField.physics.infoFriction = (1 : Real) / 40 := by
    norm_num [TrustDensityField.physics, govParamsToTrustPhysics, demoField, demoAssumptions, demoParams]
  rw [demoCert.law]
  change demoField.physics.trustElasticity ^ 2 * 4 ^ 2 +
      demoField.physics.infoFriction ^ 2 * 4 ^ 4 = (8 : Real) / 25
  rw [hSq, hD]
  norm_num

example :
    demoCert.omegaSquared ≤ 2 * demoField.physics.infoFriction ^ 2 * demoCert.k ^ 4 := by
  apply high_k_dominated_by_friction
  have hSq : demoField.physics.trustElasticity ^ 2 = (1 : Real) / 100 := by
    simpa [demoField, demoParams] using demoField.trustElasticity_sq
  have hD : demoField.physics.infoFriction = (1 : Real) / 40 := by
    norm_num [TrustDensityField.physics, govParamsToTrustPhysics, demoField, demoAssumptions, demoParams]
  change demoField.physics.trustElasticity ^ 2 ≤ demoField.physics.infoFriction ^ 2 * 4 ^ 2
  rw [hSq, hD]
  norm_num [demoCert]

example : crossoverWavenumber ((1 : Real) / 10) ((1 : Real) / 40) (by norm_num) = 4 := by
  norm_num [crossoverWavenumber]

example :
    let k_c := crossoverWavenumber ((1 : Real) / 10) ((1 : Real) / 40) (by norm_num)
    ((1 : Real) / 10) ^ 2 * k_c ^ 2 = ((1 : Real) / 40) ^ 2 * k_c ^ 4 := by
  simpa using crossover_is_balance_point ((1 : Real) / 10) ((1 : Real) / 40)
    (by norm_num) (by norm_num)

example :
    (mkStabilityBoundExport 0.1 0.025 0.99 2.0).regime = "wave-like" := by
  native_decide

example :
    (mkStabilityBoundExport 0.1 0.025 0.99 4.0).regime = "dispersion-dominated" := by
  native_decide

example :
    (mkStabilityBoundExport 0.1 0.025 0.99 2.0).candidateRho = 0.99 := by
  rfl

end HeytingLean.Tests.Bridge.Sharma
