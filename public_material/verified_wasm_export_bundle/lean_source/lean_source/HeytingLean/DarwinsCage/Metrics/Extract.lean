import HeytingLean.DarwinsCage.Backends.Interface
import HeytingLean.DarwinsCage.Physics.Quantum
import HeytingLean.DarwinsCage.Tests.CageStatus

/-!
# Metric extraction and correctness lemmas (Phase 8)

Defines the "extractors" from backend traces to Darwin's Cage metric structures,
and proves small correctness lemmas that connect extracted data to the predicates
used by Darwin's Cage theorems.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Metrics

open scoped Classical

open Backends Physics Tests

variable {L : Type*} [CompleteLattice L]

/-- Extract performance snapshot from a trace. -/
def extractPerformance (trace : Backends.Trace L) : PerformanceSnapshot :=
  trace.performance

/-- Extract correlation samples from a trace. -/
def extractCorrelations (trace : Backends.Trace L) : List (CorrelationSample L) :=
  trace.correlations

/-- `extractPerformance` agrees with the `toRepresentation` field. -/
theorem extractPerformance_eq (trace : Backends.Trace L) :
    extractPerformance trace = trace.toRepresentation.performance := rfl

/-- `extractCorrelations` agrees with the `toRepresentation` field. -/
theorem extractCorrelations_eq (trace : Backends.Trace L) :
    extractCorrelations trace = trace.toRepresentation.correlations := rfl

/-- Predicate asserting all stored correlation sample values miss the "locked" threshold. -/
def allSamplesLow (trace : Backends.Trace L) (bounds : CorrelationBounds := {}) : Prop :=
  ∀ sample ∈ trace.correlations, ¬highCorrelation sample.value bounds

theorem allLowCorrelation_of_allSamplesLow (trace : Backends.Trace L)
    (bounds : CorrelationBounds := {})
    (hLow : allSamplesLow trace bounds) :
    allLowCorrelation trace.toRepresentation bounds := by
  intro h hh f hf hHigh
  rcases hHigh with ⟨sample, hs, -, -, hLocked⟩
  exact (hLow sample hs) hLocked

theorem uncorrelatedWithTargets_of_allLowCorrelation (rep : PhysicsRepresentation L)
    (targets : List L) (bounds : CorrelationBounds := {})
    (h_targets : targets = rep.humanVars)
    (hLow : allLowCorrelation rep bounds) :
    Physics.uncorrelatedWithTargets rep targets bounds := by
  intro t ht f hf
  have ht' : t ∈ rep.humanVars := by simpa [h_targets] using ht
  exact hLow t ht' f hf

/-- If the extracted inequalities match the classifier preconditions, the status is `broken`. -/
theorem status_broken_of_trace (trace : Backends.Trace L) (t : CageThresholds) :
    t.performance ≤ trace.performance.rSquared →
      ¬t.locked ≤ trace.performance.maxCorr →
        ¬t.transition ≤ trace.performance.maxCorr →
          determineCageStatus trace.performance t = CageStatus.broken := by
  intro hPerf hNotLocked hNotTrans
  exact Tests.classify_broken (t := t)
    (maxCorr := trace.performance.maxCorr)
    (rSquared := trace.performance.rSquared)
    hPerf hNotLocked hNotTrans

end Metrics
end DarwinsCage
end HeytingLean
