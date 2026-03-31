import HeytingLean.Ontology.CoinductiveBounded.GenesisBridge

/-!
# Tests.Ontology.CoinductiveBoundedBridgeSanity

Compile-time sanity checks for ontology-routed Genesis bridge helpers.
-/

namespace HeytingLean.Tests.Ontology

open HeytingLean.Ontology.CoinductiveBounded
open HeytingLean.Genesis

example :
    0 ∈ (fromGraphToStabilized (boundedObserveGraph 0 CoGame.Life)).witness := by
  exact life_ontology_noneist_bridge.1

example :
    strictNoneismAdapter.interpretedImpossible (stabilizationFormula CoGame.Life) := by
  exact life_ontology_noneist_bridge.2.1

example :
    permissiveNoneismAdapter.interpretedClaim (stabilizationFormula CoGame.Life) := by
  exact life_ontology_noneist_bridge.2.2

example :
    regionNucleus (emergent_region_transport_data (graphWitnessInterior 0 CoGame.Life)) ≠
      emergent_region_transport_data (graphWitnessInterior 0 CoGame.Life) := by
  exact life_ontology_reentry_not_fixed.2

end HeytingLean.Tests.Ontology
