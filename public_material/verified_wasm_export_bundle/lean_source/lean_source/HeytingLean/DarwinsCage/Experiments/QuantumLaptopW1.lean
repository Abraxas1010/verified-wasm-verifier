import HeytingLean.DarwinsCage.Backends.LoFBlochBridge
import HeytingLean.DarwinsCage.Metrics.Extract
import HeytingLean.DarwinsCage.Experiments.ExpW1Quantum

/-!
# Quantum Laptop experiment (W1-style) via LoF–Bloch bridge

This is a first end-to-end "extended" experiment:

`LoFBloch` semantics → a backend trace → extracted metrics → a `QuantumScenario`
→ Darwin's Cage goal predicate.

The trace used here is intentionally minimal (empty correlations, perfect R²) to
exercise the integration pipeline without introducing physics-heavy assumptions.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Experiments

open scoped Classical

open Backends Metrics Physics

abbrev L : Type := Backends.BlochLattice

noncomputable def nucleus : Nucleus L := Backends.idNucleus

noncomputable def thresholds : CageThresholds := CageThresholds.francisco

noncomputable def bounds : CorrelationBounds := thresholds.toCorrelationBounds

noncomputable def trace : Backends.Trace L :=
  { raw := Backends.rawOfState HeytingLean.Quantum.LoFBloch.void
    humanVars := [Backends.rawOfState HeytingLean.Quantum.LoFBloch.void]
    aiFeatures := [Backends.rawOfState HeytingLean.Quantum.LoFBloch.reentry]
    correlations := []
    performance := { maxCorr := 0, rSquared := 1 } }

noncomputable def rep : PhysicsRepresentation L := trace.toRepresentation

theorem trace_allSamplesLow : Metrics.allSamplesLow trace bounds := by
  intro sample hs
  cases hs

theorem rep_allLowCorrelation : allLowCorrelation rep bounds := by
  exact Metrics.allLowCorrelation_of_allSamplesLow (trace := trace) (bounds := bounds) trace_allSamplesLow

theorem trace_uncorrelatedTargets :
    Physics.uncorrelatedWithTargets rep trace.humanVars bounds := by
  have h_targets : trace.humanVars = rep.humanVars := rfl
  exact Metrics.uncorrelatedWithTargets_of_allLowCorrelation
    (rep := rep) (targets := trace.humanVars) (bounds := bounds) h_targets rep_allLowCorrelation

noncomputable def scenario : QuantumScenario L :=
  { nucleus := nucleus
    rep := rep
    classicalTargets := trace.humanVars
    targets_eq_humanVars := rfl
    learnsQuantumDynamics := True
    learnsEvidence := trivial
    bounds := bounds
    thresholds := thresholds
    perf_ok := by
      simp [thresholds, CageThresholds.francisco, rep, trace, Backends.Trace.toRepresentation]
      norm_num
    corr_not_locked := by
      simp [thresholds, CageThresholds.francisco, rep, trace, Backends.Trace.toRepresentation]
    corr_low := by
      simp [thresholds, CageThresholds.francisco, rep, trace, Backends.Trace.toRepresentation]
    uncorrelatedTargets := trace_uncorrelatedTargets
    raw_fixed := by
      simp [nucleus, Backends.idNucleus, Quantum.Modality.idNucleus, rep, trace]
    feature_fixed := by
      intro f hf
      simp [nucleus, Backends.idNucleus, Quantum.Modality.idNucleus] }

/-- W1-style wrapper experiment built from the `scenario`. -/
noncomputable def expW1 : ExpW1Quantum L := { scenario := scenario }

end Experiments
end DarwinsCage
end HeytingLean
