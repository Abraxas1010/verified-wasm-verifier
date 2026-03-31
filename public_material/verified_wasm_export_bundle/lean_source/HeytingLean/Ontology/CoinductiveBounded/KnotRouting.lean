import HeytingLean.Ontology.CoinductiveBounded.Stabilized
import HeytingLean.Ontology.CoinductiveBounded.Observer
import HeytingLean.Topology.Knot.VirtualTransport
import HeytingLean.Topology.Knot.VirtualInvariantBridge
import HeytingLean.PerspectivalPlenum.ProjectionObligations
import HeytingLean.Topology.Knot.BracketMathlib

/-!
# Ontology.CoinductiveBounded.KnotRouting

Route the existing knot-side transport and invariant surfaces through the
coinductive bounded ontology vocabulary.

This module does not introduce new knot mathematics. It packages the already
proved Reidemeister transport and bracket-invariance results as ontology-facing
carrier transports and observation-preservation theorems.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

open HeytingLean.Genesis
open HeytingLean.Topology.Knot

/-- Ontology-facing knot witness routed through the existing K1 transport into the graph backend. -/
structure KnotRoutedWitness where
  diagram : PDGraph

namespace KnotRoutedWitness

/-- Knot states currently route into the graph backend through the `Life` co-game anchor. -/
def routedCarrier (K : KnotRoutedWitness) : GraphCarrier :=
  CoGame.reRoot CoGame.Life (Topology.Knot.omegaLifeNodeMap.toCoNode K.diagram)

@[simp] theorem routedCarrier_eq_life (K : KnotRoutedWitness) :
    K.routedCarrier = CoGame.Life := by
  cases K
  rfl

/-- Backend-tagged ontology witness associated to the routed carrier. -/
def carrierWitness (K : KnotRoutedWitness) : CarrierWitness :=
  fromCoGame K.routedCarrier

@[simp] theorem carrierWitness_backend (K : KnotRoutedWitness) :
    K.carrierWitness.backend = .graph := by
  simp [carrierWitness]

/-- Ontology observation for knot routing: bounded graph signal plus knot bracket signature. -/
abbrev Observation :=
  GraphSignal × Except String Kauffman.PolyML

/-- Combined ontology observation at depth `n`. -/
noncomputable def observation (depth : Nat) (K : KnotRoutedWitness) : Observation :=
  (boundedObserveGraph depth K.routedCarrier, bracketSignature K.diagram)

/-- Stabilized meaning obtained by routing the knot state through the graph backend. -/
noncomputable def routedStabilizedMeaning (depth : Nat) (K : KnotRoutedWitness) : StabilizedMeaning Support :=
  fromGraphToStabilized (boundedObserveGraph depth K.routedCarrier)

end KnotRoutedWitness

/-- Ontology-level carrier transport between backend-tagged witnesses. -/
structure CarrierTransport where
  source : CarrierWitness
  target : CarrierWitness

/-- TWIST transport: ontology packaging of an R2 move. -/
structure TwistTransport where
  src : KnotRoutedWitness
  dst : KnotRoutedWitness
  x : Nat
  u : Nat
  move_ok : Reidemeister.r2Add src.diagram x u = .ok dst.diagram

namespace TwistTransport

def TWIST (τ : TwistTransport) : CarrierTransport where
  source := τ.src.carrierWitness
  target := τ.dst.carrierWitness

@[simp] theorem source_backend (τ : TwistTransport) :
    τ.TWIST.source.backend = .graph := by
  simp [TWIST]

@[simp] theorem target_backend (τ : TwistTransport) :
    τ.TWIST.target.backend = .graph := by
  simp [TWIST]

theorem preserves_boundedObservation (τ : TwistTransport) (depth : Nat) :
    boundedObserveGraph depth τ.dst.routedCarrier = boundedObserveGraph depth τ.src.routedCarrier := by
  simp [KnotRoutedWitness.routedCarrier_eq_life]

theorem preserves_observation (τ : TwistTransport) (depth : Nat) :
    τ.dst.observation depth = τ.src.observation depth := by
  apply Prod.ext
  · exact τ.preserves_boundedObservation depth
  · exact virtual_class_respects_bracket_signature τ.move_ok

end TwistTransport

/--
ROTATE transport: ontology packaging of the Reidemeister-III left/right braid
endpoints together with the existing bridge witness.
-/
structure RotateTransport where
  src : KnotRoutedWitness
  left : KnotRoutedWitness
  right : KnotRoutedWitness
  x : Nat
  u : Nat
  w : Nat
  left_ok : Reidemeister.r3BraidLeft src.diagram x u w = .ok left.diagram
  right_ok : Reidemeister.r3BraidRight src.diagram x u w = .ok right.diagram
  bridge : Kauffman.R3SkeinBridgeWitness src.diagram left.diagram right.diagram x u w

namespace RotateTransport

def ROTATE_left (ρ : RotateTransport) : CarrierTransport where
  source := ρ.src.carrierWitness
  target := ρ.left.carrierWitness

def ROTATE_right (ρ : RotateTransport) : CarrierTransport where
  source := ρ.src.carrierWitness
  target := ρ.right.carrierWitness

@[simp] theorem left_backend (ρ : RotateTransport) :
    ρ.ROTATE_left.target.backend = .graph := by
  simp [ROTATE_left]

@[simp] theorem right_backend (ρ : RotateTransport) :
    ρ.ROTATE_right.target.backend = .graph := by
  simp [ROTATE_right]

theorem preserves_boundedObservation (ρ : RotateTransport) (depth : Nat) :
    boundedObserveGraph depth ρ.left.routedCarrier = boundedObserveGraph depth ρ.right.routedCarrier := by
  simp [KnotRoutedWitness.routedCarrier_eq_life]

theorem preserves_observation (ρ : RotateTransport) (depth : Nat) :
    ρ.left.observation depth = ρ.right.observation depth := by
  apply Prod.ext
  · exact ρ.preserves_boundedObservation depth
  · exact PerspectivalPlenum.ProjectionObligations.virtual_knot_transport_r3_bracket_bridge_hook
      ρ.left_ok ρ.right_ok ρ.bridge

end RotateTransport

/--
Frozen eigenform: the ontology-level observation is invariant under the available
knot transport operators routed through this ontology layer.
-/
structure FrozenEigenform (K : KnotRoutedWitness) : Prop where
  twist_preserved :
    ∀ depth, ∀ τ : TwistTransport, τ.src = K → τ.dst.observation depth = K.observation depth
  rotate_preserved :
    ∀ depth, ∀ ρ : RotateTransport, ρ.src = K → ρ.left.observation depth = ρ.right.observation depth

theorem knotWitness_is_frozen (K : KnotRoutedWitness) : FrozenEigenform K where
  twist_preserved := by
    intro depth τ hsrc
    subst hsrc
    exact τ.preserves_observation depth
  rotate_preserved := by
    intro depth ρ hsrc
    subst hsrc
    exact ρ.preserves_observation depth

/-- Canonical zero-crossing unknot graph. -/
def unknotDiagram : PDGraph :=
  { freeLoops := 1, n := 0, arcNbr := #[] }

/-- Ontology-routed unknot witness. -/
def unknotWitness : KnotRoutedWitness :=
  ⟨unknotDiagram⟩

theorem unknot_bracket_signature :
    bracketSignature unknotDiagram = .ok (1 : Kauffman.PolyML) := by
  simpa [bracketSignature, unknotDiagram] using Kauffman.bracketGraphMLAux_base 0 1

theorem unknot_trivial_stabilized_meaning :
    (unknotWitness.routedStabilizedMeaning 0).witness = ({0} : Set Nat) := by
  change (fromGraphToStabilized (boundedObserveGraph 0 CoGame.Life)).witness = ({0} : Set Nat)
  exact fromGraphToStabilized_life_zero

/--
The existing nucleus/unknot story factors through the ontology layer: the knot-side
unknot has trivial bracket signature, and the routed graph-side stabilized meaning is
the nucleus-fixed boundary witness.
-/
theorem r_nucleus_unknot_factors_through_ontology :
    unknotWitness.routedStabilizedMeaning 0 = fromGraphToStabilized (boundedObserveGraph 0 CoGame.Life) ∧
      bracketSignature unknotDiagram = .ok (1 : Kauffman.PolyML) := by
  constructor
  · simp [KnotRoutedWitness.routedStabilizedMeaning, unknotWitness]
  · exact unknot_bracket_signature

end HeytingLean.Ontology.CoinductiveBounded
