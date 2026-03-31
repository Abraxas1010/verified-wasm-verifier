import Mathlib.Data.Real.Basic
import HeytingLean.DarwinsCage.Correlation

/-!
# Cage status bookkeeping

Determines whether an AI model is LOCKED/TRANSITION/BROKEN/FAILED based on its
performance snapshot and the thresholds sourced from Francisco's experiments.
-/

namespace HeytingLean
namespace DarwinsCage

/-- Discrete cage status labels mirroring Francisco's taxonomy. -/
inductive CageStatus
  | locked
  | transition
  | broken
  | failed
  deriving DecidableEq, Repr

/-- Threshold configuration for cage classification. Extends correlation bounds with R². -/
structure CageThresholds extends CorrelationBounds where
  /-- Minimal acceptable R² before declaring the experiment a failure. -/
  performance : ℝ := (9 : ℝ) / 10

noncomputable instance : Inhabited CageThresholds := ⟨{}⟩

namespace CageThresholds

/-- Named preset matching the default values used throughout the Darwin's Cage modules. -/
noncomputable def standard : CageThresholds := {}

/-- Francisco's paper-level defaults (locked/transition from `CorrelationBounds`, performance 0.9). -/
noncomputable def francisco : CageThresholds :=
  { locked := (7 : ℝ) / 10
    transition := (1 : ℝ) / 2
    performance := (9 : ℝ) / 10 }

@[simp] theorem standard_eq : standard = ({} : CageThresholds) := rfl

end CageThresholds

/-- Determine the cage status from a performance snapshot and thresholds. -/
noncomputable def determineCageStatus (perf : PerformanceSnapshot)
    (thresholds : CageThresholds := {}) : CageStatus :=
  if perf.rSquared < thresholds.performance then
    .failed
  else if perf.maxCorr ≥ thresholds.locked then
    .locked
  else if perf.maxCorr ≥ thresholds.transition then
    .transition
  else
    .broken

end DarwinsCage
end HeytingLean
