import Mathlib
import HeytingLean.ATheory.Paper.HypergraphSpace

/-!
# Bridge.Veselov.NetworkDynamics

Assumption-first contracts connecting a universe graph and a brain graph through
shared objective-preservation hypotheses.
-/

namespace HeytingLean.Bridge.Veselov

universe u

/-- Finite objective network with explicit scoring. -/
structure NetworkObjective (V : Type u) [Fintype V] where
  transition : V → V → Prop
  score : V → ℝ
  scoreNonneg : ∀ v : V, 0 ≤ score v

abbrev UniverseNetwork (V : Type u) [Fintype V] := NetworkObjective V
abbrev BrainNetwork (V : Type u) [Fintype V] := NetworkObjective V

/-- A witness bridge that preserves scores in both directions. -/
structure NetworkBridge
    {U B : Type u} [Fintype U] [Fintype B]
    (NU : NetworkObjective (V := U)) (NB : NetworkObjective (V := B)) where
  toBrain : U → B
  toUniverse : B → U
  preserveForward : ∀ u : U, NB.score (toBrain u) = NU.score u
  preserveBackward : ∀ b : B, NU.score (toUniverse b) = NB.score b
  roundtripUniverse : ∀ u : U, toUniverse (toBrain u) = u
  roundtripBrain : ∀ b : B, toBrain (toUniverse b) = b

/-- Forward score preservation theorem. -/
theorem bridge_score_transport_forward (U B : Type u) [Fintype U] [Fintype B]
    (NU : NetworkObjective (V := U)) (NB : NetworkObjective (V := B))
    (H : NetworkBridge (U := U) (B := B) (NU := NU) (NB := NB)) :
    ∀ u : U, NB.score (H.toBrain u) = NU.score u := by
  intro u
  exact H.preserveForward u

/-- Backward score preservation theorem. -/
theorem bridge_score_transport_backward (U B : Type u) [Fintype U] [Fintype B]
    (NU : NetworkObjective (V := U)) (NB : NetworkObjective (V := B))
    (H : NetworkBridge (U := U) (B := B) (NU := NU) (NB := NB)) :
    ∀ b : B, NU.score (H.toUniverse b) = NB.score b := by
  intro b
  exact H.preserveBackward b

/-- The transport map viewed as a B-hypergraph for downstream API reuse. -/
def network_to_hypergraph (V : Type u) [Fintype V] (N : NetworkObjective (V := V)) :
    ATheory.Paper.BHypergraph.Graph where
  V := V
  U := Set.univ
  E := fun a b c => N.transition a b ∧ c = a

/-- Hypergraph edges in `network_to_hypergraph` are exactly transition witnesses with
trivial output-coding metadata. -/
theorem network_to_hypergraph_edge (V : Type u) [Fintype V] (N : NetworkObjective (V := V))
    (a b c : V) :
    (network_to_hypergraph (V := V) N).E a b c ↔ N.transition a b ∧ c = a := by
  rfl

/-- Edges always determine the transition source-target pair. -/
theorem hypergraph_edge_transition (V : Type u) [Fintype V] (N : NetworkObjective (V := V))
    (a b c : V) (h : (network_to_hypergraph (V := V) N).E a b c) :
    N.transition a b := by
  exact (network_to_hypergraph_edge (V := V) (N := N) a b c).1 h |>.1

/-- Every network transition witnesses a hyperedge in the transported graph. -/
theorem transition_witnesses_hyperedge (V : Type u) [Fintype V] (N : NetworkObjective (V := V))
    (a b : V) (h : N.transition a b) :
    (network_to_hypergraph (V := V) N).E a b a := by
  exact (network_to_hypergraph_edge (V := V) (N := N) a b a).2 ⟨h, rfl⟩

end HeytingLean.Bridge.Veselov
