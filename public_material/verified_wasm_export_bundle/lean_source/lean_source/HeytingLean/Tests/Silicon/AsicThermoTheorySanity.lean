import HeytingLean.Silicon

namespace HeytingLean.Tests.Silicon
namespace AsicThermoTheorySanity

open HeytingLean
open HeytingLean.Probability.InfoTheory
open HeytingLean.Silicon

noncomputable section

def demoRun : Run Bool Bool :=
  FinDist.prod Silicon.Examples.unifBool Silicon.Examples.unifBool

def demoSignature : AsicThermoTheory.ThermoSignature Bool Bool where
  run := demoRun
  leakage := 0
  leakageNonNeg := by norm_num
  signalEnergy := 2
  signalEnergyNonNeg := by norm_num

example :
    0 ≤ AsicThermoTheory.reservoirInformation (S := Bool) (O := Bool) demoSignature := by
  simpa using AsicThermoTheory.reservoirInformation_nonneg (S := Bool) (O := Bool) demoSignature

def partialGain : AsicThermoTheory.EarlyAbortGain where
  totalEnergy := 10
  savedEnergy := 3
  totalPos := by norm_num
  saveNonNeg := by norm_num
  saveLeTotal := by norm_num

example : 0 ≤ AsicThermoTheory.earlyAbortGain partialGain := by
  exact AsicThermoTheory.earlyAbortGain_nonneg partialGain

example : AsicThermoTheory.earlyAbortGain partialGain ≤ 1 := by
  exact AsicThermoTheory.earlyAbortGain_le_one partialGain

def fullSaving : AsicThermoTheory.EarlyAbortGain where
  totalEnergy := 7
  savedEnergy := 7
  totalPos := by norm_num
  saveNonNeg := by norm_num
  saveLeTotal := by norm_num

example : AsicThermoTheory.earlyAbortGain fullSaving = 0 := by
  simpa using AsicThermoTheory.earlyAbortGain_full_saving_eq_zero fullSaving rfl

def noSaving : AsicThermoTheory.EarlyAbortGain where
  totalEnergy := 7
  savedEnergy := 0
  totalPos := by norm_num
  saveNonNeg := by norm_num
  saveLeTotal := by norm_num

example : AsicThermoTheory.earlyAbortGain noSaving = 1 := by
  simpa using AsicThermoTheory.earlyAbortGain_no_saving_eq_one noSaving rfl

def demoEmpirical : AsicThermoTheory.ThermalEmpiricalContract where
  edgeChaosCV := 0.092
  cvInOpenInterval := by constructor <;> norm_num
  nrmse := 0.8661
  nrmseNonneg := by norm_num
  gainClaimed := 0.885
  gainClaimedNonneg := by norm_num
  provenanceHash := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
  runId := "thermal_demo_20260220"
  sourceUrl := "https://arxiv.org/abs/2601.01916"

example : AsicThermoTheory.thermalEmpiricalReady demoEmpirical := by
  exact AsicThermoTheory.thermalEmpiricalReady_of_fields demoEmpirical (by decide) (by decide) (by decide)

end
end AsicThermoTheorySanity
end HeytingLean.Tests.Silicon
