import HeytingLean.DarwinsCage.Physics.Quantum

/-!
# Experiment W1 (Quantum) scaffold

Simple wrapper around `QuantumScenario` representing the W1 experiment. Later
proofs will provide concrete instantiations and show the goal holds.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Experiments

open Physics

/-- Metadata for Francisco's Experiment W1. -/
structure ExpW1Quantum (L : Type*) [CompleteLattice L] [HeytingAlgebra L] where
  scenario : QuantumScenario L
  notes : String := "Quantum W1 experiment (Heyting image of OML)."

/-- Desired goal: W1 satisfies the cage-breaking criterion. -/
def ExpW1Quantum.goal {L : Type*} [CompleteLattice L] [HeytingAlgebra L]
    (exp : ExpW1Quantum L) : Prop :=
  exp.scenario.cageBreakingGoal

end Experiments
end DarwinsCage
end HeytingLean
