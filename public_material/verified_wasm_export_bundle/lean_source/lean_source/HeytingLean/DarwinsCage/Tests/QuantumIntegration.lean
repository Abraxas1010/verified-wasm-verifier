import Mathlib.Tactic.NormNum
import HeytingLean.DarwinsCage.Theorems.QuantumLearning
import HeytingLean.DarwinsCage.QuantumModality
import HeytingLean.Quantum.OML.Examples.O6

/-!
# Quantum integration smoke test

This test imports an existing quantum translation nucleus and shows that we can
instantiate a Darwin's Cage `QuantumScenario` over that lattice and discharge
the experiment goal using the generic theorem.

The point here is integration: Darwin's Cage compiles against the quantum stack
without introducing proof holes.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Tests

open Physics Experiments Theorems

noncomputable section

namespace QuantumIntegration

open HeytingLean.Quantum.OML

def R : Nucleus (Set O6) := Quantum.Modality.idNucleus (Set O6)

def rep : PhysicsRepresentation (Set O6) :=
  { raw := R (∅)
    humanVars := []
    aiFeatures := []
    correlations := []
    performance := { maxCorr := 0, rSquared := 1 } }

def thresholds : CageThresholds := CageThresholds.francisco

def scenario : QuantumScenario (Set O6) :=
  { nucleus := R
    rep := rep
    classicalTargets := []
    targets_eq_humanVars := rfl
    learnsQuantumDynamics := True
    learnsEvidence := trivial
    bounds := {}
    thresholds := thresholds
    perf_ok := by
      dsimp [thresholds, CageThresholds.francisco, rep]
      norm_num
    corr_not_locked := by
      dsimp [thresholds, CageThresholds.francisco, rep]
      norm_num
    corr_low := by
      dsimp [thresholds, CageThresholds.francisco, rep]
      norm_num
    uncorrelatedTargets := by
      intro t ht
      cases ht
    raw_fixed := by
      simp [rep, R, Quantum.Modality.idNucleus]
    feature_fixed := by
      intro f hf
      cases hf }

def expW1 : ExpW1Quantum (Set O6) := { scenario := scenario }

theorem expW1_smoke : expW1.goal :=
  Theorems.expW1_quantum_breaks_cage expW1

end QuantumIntegration

end

end Tests
end DarwinsCage
end HeytingLean
