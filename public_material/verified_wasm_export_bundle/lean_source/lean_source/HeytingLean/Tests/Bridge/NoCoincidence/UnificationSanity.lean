import HeytingLean.Bridge.NoCoincidence

open HeytingLean.Bridge.NoCoincidence.Basic
open HeytingLean.Bridge.NoCoincidence.Nucleus
open HeytingLean.Bridge.NoCoincidence.Bridge
open HeytingLean.HossenfelderNoGo.HeytingBoundary

namespace HeytingLean.Tests.Bridge.NoCoincidence

#check wolfram_independence_parallel
#check circuit_heyting_gap_and_non_boolean
#check WolframIndependence

example :
    ∃ C : RevCircuit 1, C ∈ circuitHeytingGap (sizeNucleus 1) (PropertyP 1) := by
  refine ⟨RevCircuit.identity 1, ?_⟩
  constructor
  · exact Or.inr (by
      simp [sizeNucleus, mkFocusNucleus, smallCircuit, RevCircuit.size, RevCircuit.identity])
  · exact identity_fails_P 1 (by decide)

example (hBridge : BooleanBoundaryBridge (circuitBoundaryNucleus (sizeNucleus 1))) :
    ¬ isBoolean (circuitBoundaryNucleus (sizeNucleus 1)) := by
  exact circuit_boundary_non_boolean (sizeNucleus 1) hBridge

example (hBridge : BooleanBoundaryBridge (circuitBoundaryNucleus (sizeNucleus 1))) :
    boundaryGap (circuitBoundaryNucleus (sizeNucleus 1)) (PropertyP 1) ≠ ∅ ∧
    ¬ isBoolean (circuitBoundaryNucleus (sizeNucleus 1)) := by
  apply circuit_heyting_gap_and_non_boolean (sizeNucleus 1) (PropertyP 1)
  · refine ⟨RevCircuit.identity 1, ?_⟩
    constructor
    · exact Or.inr (by
        simp [sizeNucleus, mkFocusNucleus, smallCircuit, RevCircuit.size, RevCircuit.identity])
    · exact identity_fails_P 1 (by decide)
  · exact hBridge

end HeytingLean.Tests.Bridge.NoCoincidence
