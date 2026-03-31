import HeytingLean.DarwinsCage.Experiments.Exp2Relativity
import HeytingLean.DarwinsCage.Experiments.Exp3Phase
import HeytingLean.DarwinsCage.Experiments.ExpB3Entanglement
import HeytingLean.DarwinsCage.Experiments.ExpW1Quantum

/-!
# Experiment summary scaffolding

Aggregates the individual experiment metadata and goal statements so downstream
documentation/tests can reference them from a single namespace.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Experiments

/-- Bundle of the key experiments covered in the Darwin's Cage formalization. -/
structure Summary where
  exp2 : Exp2Relativity
  exp3 : ∀ {L : Type*} [CompleteLattice L] [HeytingAlgebra L], Exp3Phase L
  expB3 : ∀ {L : Type*} [CompleteLattice L] [HeytingAlgebra L], ExpB3Entanglement L
  expW1 : ∀ {L : Type*} [CompleteLattice L] [HeytingAlgebra L], ExpW1Quantum L

/-- Combined goal asserting that every experiment attains its cage-breaking condition. -/
def Summary.allGoals (s : Summary) : Prop :=
  s.exp2.goal ∧
    (∀ {L : Type*} [CompleteLattice L] [HeytingAlgebra L],
      (s.exp3 : Exp3Phase L).goal ∧ (s.expB3 : ExpB3Entanglement L).goal ∧
        (s.expW1 : ExpW1Quantum L).goal)

end Experiments
end DarwinsCage
end HeytingLean
