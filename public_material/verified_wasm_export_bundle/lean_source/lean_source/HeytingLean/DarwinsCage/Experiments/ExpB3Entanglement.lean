import HeytingLean.DarwinsCage.Physics.Quantum

/-!
# Experiment B3 (Entanglement) scaffold

Captures the entanglement-specific scenario described by Francisco and plugs into
the quantum cage-breaking predicates.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Experiments

open Physics

/-- Metadata for the entanglement (B3) experiment. -/
structure ExpB3Entanglement (L : Type*) [CompleteLattice L] [HeytingAlgebra L] where
  scenario : QuantumScenario L
  description : String :=
    "Entanglement features decorrelated from classical observables."

/-- Target proposition stating that the entanglement experiment achieves cage breaking. -/
def ExpB3Entanglement.goal {L : Type*} [CompleteLattice L] [HeytingAlgebra L]
    (exp : ExpB3Entanglement L) : Prop :=
  exp.scenario.cageBreakingGoal

end Experiments
end DarwinsCage
end HeytingLean
