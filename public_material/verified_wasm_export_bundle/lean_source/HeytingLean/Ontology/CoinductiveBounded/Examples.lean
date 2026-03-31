import HeytingLean.Ontology.CoinductiveBounded.Stabilized

/-!
# Ontology.CoinductiveBounded.Examples

Named witness families demonstrating both ontology backends.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

open HeytingLean.Genesis

/-- Canonical graph witness: `Life`. -/
def lifeWitness : CarrierWitness :=
  fromCoGame CoGame.Life

/-- Nontrivial finite cycle witness. -/
def cycleWitness (n : Nat) : CarrierWitness :=
  fromCoGame (cycleCoGame n)

/-- Canonical coalgebra witness: the two-state bit-flip DFA. -/
def coalgebraWitness : CarrierWitness :=
  CoalgebraExamples.bitFlipWitness

@[simp] theorem lifeWitness_backend :
    lifeWitness.backend = .graph :=
  rfl

@[simp] theorem cycleWitness_backend (n : Nat) :
    (cycleWitness n).backend = .graph :=
  rfl

@[simp] theorem coalgebraWitness_backend :
    coalgebraWitness.backend = .coalgebra :=
  rfl

@[simp] theorem cycleWitness_head_is_void :
    (boundedObserveGraph 2 (cycleCoGame 2)).1 = .void := by
  simp [boundedObserveGraph, oscillationExpr, cycleCoGame, succOnFin]

@[simp] theorem lifeWitness_support_nonempty :
    0 ∈ (fromGraphToStabilized (boundedObserveGraph 0 CoGame.Life)).witness := by
  simp [fromGraphToStabilized_life_zero]

@[simp] theorem coalgebraWitness_support_nonempty :
    0 ∈ (fromCoalgebraToStabilized 1 false [true]).witness := by
  simp [fromCoalgebraToStabilized_false_true_zero]

end HeytingLean.Ontology.CoinductiveBounded
