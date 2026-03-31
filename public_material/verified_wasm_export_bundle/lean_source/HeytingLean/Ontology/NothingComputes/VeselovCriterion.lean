import HeytingLean.Ontology.NothingComputes.ConsciousnessTower
import HeytingLean.Bridge.Veselov.Consciousness

namespace HeytingLean.Ontology.NothingComputes

open HeytingLean.Representations.Radial

/-- Concrete substrate model used for the measurable-threshold lane. -/
structure SubstrateModel (G : RadialGraph) where
  width : Nat
  order : Nat
  tower : SelfModelTower G

/-- Observable proxy for reflective workload. Retained as an explicit bridge datum even though
the measurable threshold below no longer depends on it.
-/
def reflectiveLoad {G : RadialGraph} (system : SubstrateModel G) : Nat :=
  system.width ^ system.order

/-- Observable proxy for available assembly budget. Retained as an explicit bridge datum even
though the measurable threshold below no longer depends on it.
-/
def assemblyBudget {G : RadialGraph} (system : SubstrateModel G) : Nat :=
  Nat.factorial (system.width + system.order)

/-- The honest discriminating threshold available on this surrogate surface: the tower has at
least two reflective levels. The factorial-vs-power dominance law remains available separately as
bridge data, but it is universal and therefore not part of the threshold predicate itself.
-/
def measurableConsciousnessThreshold {G : RadialGraph} (system : SubstrateModel G) : Prop :=
  system.tower.multiLevel

theorem reflectiveLoad_le_assemblyBudget {G : RadialGraph} (system : SubstrateModel G) :
    reflectiveLoad system ≤ assemblyBudget system := by
  simpa [reflectiveLoad, assemblyBudget] using
    HeytingLean.Bridge.Veselov.intelligenceDominance_holds system.width system.order

theorem threshold_implies_measurable_self_model {G : RadialGraph} (system : SubstrateModel G)
    (h : measurableConsciousnessThreshold system) :
    ∃ i j : Fin system.tower.reflectiveDepth, i ≠ j := by
  exact HeytingLean.Ontology.NothingComputes.multiLevel_has_two_layers system.tower h

end HeytingLean.Ontology.NothingComputes
