import HeytingLean.Ontology.CoinductiveBounded.Examples
import HeytingLean.Genesis.ReentryTransport

/-!
# Ontology.CoinductiveBounded.GenesisBridge

Small, honest adapters from the ontology layer into existing Genesis plenum and
reentry-transport surfaces.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

open HeytingLean.Genesis

/-- Repackage a graph witness as the existing `WitnessInterior` surface. -/
def graphWitnessInterior (depth : Nat) (G : GraphCarrier) : Genesis.WitnessInterior where
  source := G
  depth := depth.succ
  postReentry := Nat.succ_pos depth

@[simp] theorem graphWitnessInterior_source (depth : Nat) (G : GraphCarrier) :
    (graphWitnessInterior depth G).source = G :=
  rfl

@[simp] theorem graphWitnessInterior_depth (depth : Nat) (G : GraphCarrier) :
    (graphWitnessInterior depth G).depth = depth.succ :=
  rfl

@[simp] theorem graphWitnessInterior_life (depth : Nat) :
    graphWitnessInterior depth CoGame.Life = lifeInterior depth :=
  rfl

/-- The ontology adapter preserves the existing base-stabilization predicate. -/
theorem graphWitnessInterior_baseStabilizes_iff (depth : Nat) (G : GraphCarrier) :
    Genesis.baseStabilizes (graphWitnessInterior depth G).source ↔ Genesis.baseStabilizes G := by
  simp [graphWitnessInterior]

/--
Ontology-routed noneist bridge for `Life`: combine the ontology stabilization witness
with the existing strict/permissive noneist reading.
-/
theorem life_ontology_noneist_bridge :
    0 ∈ (fromGraphToStabilized (boundedObserveGraph 0 CoGame.Life)).witness ∧
      strictNoneismAdapter.interpretedImpossible (stabilizationFormula CoGame.Life) ∧
      permissiveNoneismAdapter.interpretedClaim (stabilizationFormula CoGame.Life) := by
  exact ⟨lifeWitness_support_nonempty, life_noneist_bridge.1, life_noneist_bridge.2⟩

/--
Ontology-routed reentry transport witness for `Life`: the same graph witness that
produces the ontology boundary element remains non-fixed under the existing emergent
region transport.
-/
theorem life_ontology_reentry_not_fixed :
    0 ∈ (fromGraphToStabilized (boundedObserveGraph 0 CoGame.Life)).witness ∧
      regionNucleus (emergent_region_transport_data (graphWitnessInterior 0 CoGame.Life)) ≠
        emergent_region_transport_data (graphWitnessInterior 0 CoGame.Life) := by
  constructor
  · exact lifeWitness_support_nonempty
  · simpa [graphWitnessInterior, lifeInterior] using emergent_region_transport_life_not_fixed

end HeytingLean.Ontology.CoinductiveBounded
