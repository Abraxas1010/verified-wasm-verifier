import Mathlib.Combinatorics.SimpleGraph.Trails
import HeytingLean.Bridges.Graph
import HeytingLean.Epistemic.Occam
import HeytingLean.LoF.Axioms.GenerativeLaws

namespace HeytingLean
namespace Crypto
namespace NECP

open scoped Classical

namespace OccamEulerian

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [Fintype G.edgeSet]

/-- Concrete traversal carrier for the Eulerian/Occam comparison lane. -/
abbrev Traversal (G : SimpleGraph V) (u v : V) := G.Walk u v

/-- A traversal covers all observable edges if every graph edge appears in its edge list. -/
def coversAllEdges {u v : V} (p : Traversal G u v) : Prop :=
  ∀ e, e ∈ G.edgeSet → e ∈ p.edges

/-- Occam score for a traversal: the number of edge-observations it uses. -/
def occamScore {u v : V} (p : Traversal G u v) : Nat :=
  p.length

/-- Eulerian traversals are the all-edges walks with no repetitions. -/
def isEulerian {u v : V} (p : Traversal G u v) : Prop :=
  p.IsEulerian

/-- Traversal complexity is the same edge-budget measured by the Occam score. -/
def traversalComplexity {u v : V} (p : Traversal G u v) : Nat :=
  occamScore p

/-- A traversal is Occam-minimal if no other all-edge traversal uses fewer observations. -/
def OccamMinimal {u v : V} (p : Traversal G u v) : Prop :=
  ∀ {u' v'} (q : G.Walk u' v'), coversAllEdges q → occamScore p ≤ occamScore q

theorem edge_card_le_of_coversAllEdges {u v : V} {p : Traversal G u v}
    (hp : coversAllEdges p) :
    G.edgeFinset.card ≤ p.length := by
  have hsubset : G.edgeFinset ⊆ p.edges.toFinset := by
    intro e he
    exact by
      simpa using hp e (by simpa using he)
  calc
    G.edgeFinset.card ≤ p.edges.toFinset.card := Finset.card_le_card hsubset
    _ ≤ p.edges.length := List.toFinset_card_le p.edges
    _ = p.length := SimpleGraph.Walk.length_edges p

omit [Fintype G.edgeSet] in
theorem coversAllEdges_of_eulerian {u v : V} {p : Traversal G u v}
    (hp : isEulerian p) :
    coversAllEdges p := by
  intro e he
  exact (hp.mem_edges_iff).2 he

theorem eulerian_length_eq_card_edges {u v : V} {p : Traversal G u v}
    (hp : isEulerian p) :
    p.length = G.edgeFinset.card := by
  apply le_antisymm
  · exact hp.isTrail.length_le_card_edgeFinset
  · exact edge_card_le_of_coversAllEdges (coversAllEdges_of_eulerian hp)

theorem eulerian_is_occam_minimal {u v : V} {p : Traversal G u v}
    (hp : isEulerian p) :
    OccamMinimal p := by
  intro u' v' q hq
  have hpLen : p.length = G.edgeFinset.card := eulerian_length_eq_card_edges hp
  calc
    p.length = G.edgeFinset.card := hpLen
    _ ≤ q.length := edge_card_le_of_coversAllEdges hq

section LensBridge

open HeytingLean

variable {α : Type*} [LoF.PrimaryAlgebra α]

/-- Simple graph induced by the graph-lens comparability relation. -/
def comparabilityGraph (M : Bridges.Graph.Model α) : SimpleGraph α where
  Adj a b := a ≠ b ∧ (M.adjacency a b ∨ M.adjacency b a)
  symm := by
    intro a b hab
    rcases hab with ⟨hneq, hcomp⟩
    refine ⟨hneq.symm, ?_⟩
    cases hcomp with
    | inl hab' => exact Or.inr hab'
    | inr hba' => exact Or.inl hba'
  loopless := by
    intro a ha
    exact ha.1 rfl

/-- The graph-lens carrier supplies concrete adjacency edges for the combinatorial traversal lane. -/
def graphLensEdgeTraversal (M : Bridges.Graph.Model α) {a b : α}
    (hneq : a ≠ b) (hab : M.adjacency a b) :
    Traversal (comparabilityGraph M) a b :=
  Walk.cons ⟨hneq, Or.inl hab⟩ Walk.nil

@[simp] theorem traversalComplexity_graphLensEdgeTraversal
    (M : Bridges.Graph.Model α) {a b : α}
    (hneq : a ≠ b) (hab : M.adjacency a b) :
    traversalComplexity (graphLensEdgeTraversal M hneq hab) = 1 := by
  simp [graphLensEdgeTraversal, traversalComplexity, occamScore]

theorem graphLensTraversalBridge (M : Bridges.Graph.Model α) {a b : α}
    (hneq : a ≠ b) (hab : M.adjacency a b) :
    ∃ p : Traversal (comparabilityGraph M) a b, traversalComplexity p = 1 := by
  exact ⟨graphLensEdgeTraversal M hneq hab, traversalComplexity_graphLensEdgeTraversal M hneq hab⟩

end LensBridge

end OccamEulerian

end NECP
end Crypto
end HeytingLean
