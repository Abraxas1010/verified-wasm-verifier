import HeytingLean.Quantum.Phase
import HeytingLean.Quantum.VacuumOmegaR

/-
Compile-only sanity checks for the phase layer.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum

-- Check the minimal phase form is available.
#check Phase.minimalPhaseForm

-- Global neutrality of the minimal phase integral.
#check Phase.minimalPhase_globally_neutral

-- Local nontriviality on [0, 2π).
#check Phase.minimalPhase_locally_nontrivial

-- Check the phase-coherence predicate and vacuum lemma.
#check Phase.PhaseCoherent
#check Phase.vacuum_phase_coherent

end HeytingLean.Tests.Quantum
