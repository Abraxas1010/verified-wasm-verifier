import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Continual Metrics Contract Layer

Contract-level Lean interface for accuracy/forgetting metrics used in continual
learning experiments. This module keeps theoremized metric shape/range
properties separate from empirical estimators.
-/

namespace HeytingLean
namespace Analysis

open scoped BigOperators

/-- Contract interface for accuracy matrix and derived forgetting summaries. -/
structure ContinualMetricsContract (K : Nat) where
  /-- Accuracy matrix `R_{k,j}`: after training task `k`, evaluate on task `j`. -/
  accuracy : Fin K → Fin K → ℝ
  /-- Matrix entries are valid accuracies. -/
  accuracy_bounded : ∀ k j, 0 ≤ accuracy k j ∧ accuracy k j ≤ 1
  /-- Per-task peak accuracy summary (provided by runtime/logging layer). -/
  peak : Fin K → ℝ
  /-- Per-task final accuracy summary (provided by runtime/logging layer). -/
  final : Fin K → ℝ
  /-- Peak/final consistency contract. -/
  peak_spec : ∀ j, final j ≤ peak j ∧ peak j ≤ 1
  /-- Final accuracies remain in range. -/
  final_spec : ∀ j, 0 ≤ final j

namespace ContinualMetricsContract

variable {K : Nat} (C : ContinualMetricsContract K)

/-- Per-task forgetting as max-drop surrogate (`peak - final`). -/
def forgettingAt (j : Fin K) : ℝ :=
  C.peak j - C.final j

/-- Aggregate forgetting mass across tasks. -/
def totalForgetting : ℝ :=
  ∑ j : Fin K, C.forgettingAt j

/-- Contract theorem: accuracy matrix entries are in `[0, 1]`. -/
theorem accuracy_matrix_shape_contract (k j : Fin K) :
    0 ≤ C.accuracy k j ∧ C.accuracy k j ≤ 1 :=
  C.accuracy_bounded k j

/-- Contract theorem: forgetting is nonnegative for each task. -/
theorem forgetting_metric_nonneg (j : Fin K) :
    0 ≤ C.forgettingAt j := by
  unfold forgettingAt
  linarith [C.peak_spec j |>.1]

/-- Contract theorem: forgetting is bounded above by `1`. -/
theorem forgetting_metric_le_one (j : Fin K) :
    C.forgettingAt j ≤ 1 := by
  unfold forgettingAt
  have hpeak_le : C.peak j ≤ 1 := (C.peak_spec j).2
  have hfinal_nonneg : 0 ≤ C.final j := C.final_spec j
  linarith

/-- Contract theorem: total forgetting is nonnegative. -/
theorem total_forgetting_nonneg : 0 ≤ C.totalForgetting := by
  unfold totalForgetting
  exact Finset.sum_nonneg (fun j _ => C.forgetting_metric_nonneg j)

end ContinualMetricsContract

end Analysis
end HeytingLean
