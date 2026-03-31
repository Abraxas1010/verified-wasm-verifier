import Mathlib
import HeytingLean.Silicon.Model
import HeytingLean.Silicon.Leakage

/-!
# Silicon.AsicThermoTheory

Compact executable contracts for the thermal-reservoir thesis:
- reservoir state and signature signal,
- bounded information objective,
- and explicit early-abort energy-gain bookkeeping.
-/

namespace HeytingLean.Silicon

namespace AsicThermoTheory

universe u

open scoped BigOperators
open HeytingLean.Probability.InfoTheory

/-- Thermodynamic signal model for an ASIC-reservoir step.
All numerical assumptions are explicit to avoid hidden claims.
-/
structure ThermoSignature (S O : Type u) [Fintype S] [Fintype O] where
  run : Run S O
  leakage : ℝ
  leakageNonNeg : 0 ≤ leakage
  signalEnergy : ℝ
  signalEnergyNonNeg : 0 ≤ signalEnergy

/-- Total information proxy used by the TRC thesis.
This is not a claim about physics quality—just an auditable bookkeeping
identity under explicit assumptions.
-/
def reservoirInformation (S O : Type u) [Fintype S] [Fintype O] (R : ThermoSignature S O) : ℝ :=
  R.leakage + R.signalEnergy

/-- Nonnegativity of the reservoir information metric under assumptions. -/
theorem reservoirInformation_nonneg (S O : Type u) [Fintype S] [Fintype O] (R : ThermoSignature S O) :
    0 ≤ reservoirInformation (S := S) (O := O) R := by
  dsimp [reservoirInformation]
  exact add_nonneg R.leakageNonNeg R.signalEnergyNonNeg

/-- Concrete early-abort contract with explicit energy accounting.
 - `totalEnergy` is the baseline run cost,
 - `savedEnergy` is energy avoided by early termination.
-/
structure EarlyAbortGain where
  totalEnergy : ℝ
  savedEnergy : ℝ
  totalPos : 0 < totalEnergy
  saveNonNeg : 0 ≤ savedEnergy
  saveLeTotal : savedEnergy ≤ totalEnergy

/-- Estimated gain from early-abort as a fraction in [0,1]. -/
noncomputable def earlyAbortGain (A : EarlyAbortGain) : ℝ :=
  1 - (A.savedEnergy / A.totalEnergy)

/-- The gain is bounded below by 0 under nonnegativity assumptions. -/
theorem earlyAbortGain_nonneg (A : EarlyAbortGain) : 0 ≤ earlyAbortGain A := by
  dsimp [earlyAbortGain]
  have hratio_le_one : A.savedEnergy / A.totalEnergy ≤ 1 := by
    have hden : 0 ≤ (1 / A.totalEnergy) := by
      exact div_nonneg (show 0 ≤ (1 : ℝ) by norm_num) (le_of_lt A.totalPos)
    have hmul : A.savedEnergy / A.totalEnergy ≤ A.totalEnergy / A.totalEnergy := by
      have hmul' := mul_le_mul_of_nonneg_right A.saveLeTotal hden
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul'
    calc
      A.savedEnergy / A.totalEnergy ≤ A.totalEnergy / A.totalEnergy := hmul
      _ = 1 := by field_simp [A.totalPos.ne']
  have hratio_nonneg : 0 ≤ A.savedEnergy / A.totalEnergy := by
    exact div_nonneg A.saveNonNeg (le_of_lt A.totalPos)
  nlinarith

/-- The gain is at most 1 for the same assumptions. -/
theorem earlyAbortGain_le_one (A : EarlyAbortGain) : earlyAbortGain A ≤ 1 := by
  dsimp [earlyAbortGain]
  have hratio_nonneg : 0 ≤ A.savedEnergy / A.totalEnergy := by
    exact div_nonneg A.saveNonNeg (le_of_lt A.totalPos)
  have hratio_le_one : A.savedEnergy / A.totalEnergy ≤ 1 := by
    have hden : 0 ≤ (1 / A.totalEnergy) := by
      exact div_nonneg (show 0 ≤ (1 : ℝ) by norm_num) (le_of_lt A.totalPos)
    have hmul : A.savedEnergy / A.totalEnergy ≤ A.totalEnergy / A.totalEnergy := by
      have hmul' := mul_le_mul_of_nonneg_right A.saveLeTotal hden
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul'
    calc
      A.savedEnergy / A.totalEnergy ≤ A.totalEnergy / A.totalEnergy := hmul
      _ = 1 := by field_simp [A.totalPos.ne']
  nlinarith

/-- Empirical constants and benchmark claims are represented as a typed evidence package. -/
structure ThermalEmpiricalContract where
  edgeChaosCV : ℝ
  cvInOpenInterval : 0 ≤ edgeChaosCV ∧ edgeChaosCV ≤ 1
  nrmse : ℝ
  nrmseNonneg : 0 ≤ nrmse
  gainClaimed : ℝ
  gainClaimedNonneg : 0 ≤ gainClaimed
  provenanceHash : String
  runId : String
  sourceUrl : String

/-- Empirical payload is admissible only with explicit provenance metadata. -/
def thermalEmpiricalReady (T : ThermalEmpiricalContract) : Prop :=
  T.provenanceHash ≠ "" ∧ T.runId ≠ "" ∧ T.sourceUrl ≠ ""

theorem thermalEmpiricalReady_of_fields (T : ThermalEmpiricalContract)
    (hHash : T.provenanceHash ≠ "") (hRun : T.runId ≠ "") (hUrl : T.sourceUrl ≠ "") :
    thermalEmpiricalReady T := ⟨hHash, hRun, hUrl⟩

/-- `savedEnergy = totalEnergy` makes the gain fraction reduce to `0`. -/
theorem earlyAbortGain_full_saving_eq_zero (A : EarlyAbortGain) (h : A.savedEnergy = A.totalEnergy) :
    earlyAbortGain A = 0 := by
  dsimp [earlyAbortGain]
  rw [h, div_self (by exact ne_of_gt A.totalPos)]
  simp

/-- `savedEnergy = 0` makes the gain fraction reduce to `1`. -/
theorem earlyAbortGain_no_saving_eq_one (A : EarlyAbortGain) (h : A.savedEnergy = 0) :
    earlyAbortGain A = 1 := by
  dsimp [earlyAbortGain]
  rw [h]
  simp

end AsicThermoTheory

end HeytingLean.Silicon
