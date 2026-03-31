import HeytingLean.Ontology.CoinductiveBounded

/-!
# Tests.Ontology.CoinductiveBoundedKnotRoutingSanity

Compile-time sanity checks for ontology-routed knot transport.
-/

namespace HeytingLean.Tests.Ontology

open HeytingLean.Ontology.CoinductiveBounded
open HeytingLean.Topology.Knot

#check KnotRoutedWitness
#check FrozenEigenform
#check TwistTransport.TWIST
#check RotateTransport.ROTATE_left
#check RotateTransport.ROTATE_right

example :
    unknotWitness.carrierWitness.backend = .graph :=
  KnotRoutedWitness.carrierWitness_backend unknotWitness

example :
    KnotRoutedWitness.routedCarrier unknotWitness = HeytingLean.Genesis.CoGame.Life := by
  simp [unknotWitness]

example :
    bracketSignature unknotDiagram = .ok (1 : Kauffman.PolyML) :=
  unknot_bracket_signature

example :
    (unknotWitness.routedStabilizedMeaning 0).witness = ({0} : Set Nat) :=
  unknot_trivial_stabilized_meaning

example :
    FrozenEigenform unknotWitness :=
  knotWitness_is_frozen unknotWitness

example :
    unknotWitness.routedStabilizedMeaning 0 = fromGraphToStabilized (boundedObserveGraph 0 HeytingLean.Genesis.CoGame.Life) := by
  exact r_nucleus_unknot_factors_through_ontology.1

example :
    bracketSignature unknotDiagram = .ok (1 : Kauffman.PolyML) := by
  exact r_nucleus_unknot_factors_through_ontology.2

example {src dst : KnotRoutedWitness} {x u : Nat}
    (h : Reidemeister.r2Add src.diagram x u = .ok dst.diagram) :
    dst.observation 0 = src.observation 0 := by
  let τ : TwistTransport := { src := src, dst := dst, x := x, u := u, move_ok := h }
  exact τ.preserves_observation 0

end HeytingLean.Tests.Ontology
