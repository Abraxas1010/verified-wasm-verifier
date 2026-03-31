import HeytingLean.LoF.ReEntry
import HeytingLean.FractalUniverse.Core.DynamicGraph

/-!
# Graph Growth as Re-Entry

Connects Veselov's graph growth model to Spencer-Brown's Laws of Form
re-entry concept as formalized in HeytingLean.LoF.ReEntry.

The key structural analogy: the growing graph G(t+1) contains G(t)
via the growth injection, making the sequence of graphs a form that
re-enters itself at each step. The irreversibility of growth
(no edge-preserving retraction from V(t+1) to V(t)) corresponds to
the irreversibility of the ratchet / arrow of time.
-/

namespace HeytingLean.FractalUniverse.NucleusConnection

/-- Graph growth as LoF re-entry: the growing graph contains all previous
    forms via injective embeddings that preserve the causal structure. -/
structure ReEntryGrowth (G : Core.DynamicGraph) where
  /-- Each growth step embeds the old graph into the new one,
      preserving all causal edges. This is the re-entry: G(t) ⊂ G(t+1). -/
  containment : ∀ t, ∃ (ι : G.V t ↪ G.V (t + 1)),
    ∀ u v, G.E t u v → G.E (t + 1) (ι u) (ι v)

/-- Every DynamicGraph has the re-entry containment property,
    via the built-in growth map. -/
theorem dynamic_graph_has_reentry (G : Core.DynamicGraph) :
    ∀ t, ∃ (ι : G.V t ↪ G.V (t + 1)),
      ∀ u v, G.E t u v → G.E (t + 1) (ι u) (ι v) := by
  intro t
  exact ⟨⟨G.growth t, G.growth_injective t⟩, G.growth_preserves_edges t⟩

/-- Construct a ReEntryGrowth witness for any DynamicGraph. -/
def mkReEntryGrowth (G : Core.DynamicGraph) : ReEntryGrowth G where
  containment := dynamic_graph_has_reentry G

/-- Growth is irreversible (cardinality): the vertex count is strictly
    increasing, so no injection from V(t+1) into V(t) exists at all.
    This is stronger than edge-preservation irreversibility — not even
    a set-theoretic injection is possible, regardless of edge structure. -/
theorem growth_irreversible (G : Core.DynamicGraph) (t : ℕ)
    [Fintype (G.V t)] [Fintype (G.V (t + 1))] :
    ¬ ∃ (_ : G.V (t + 1) ↪ G.V t), True := by
  intro ⟨π', _⟩
  have h1 := Core.monotone_vertex_count G t
  have h2 := Fintype.card_le_of_embedding π'
  omega

/-- Growth is irreversible (causal): no edge-preserving embedding from
    V(t+1) back into V(t) exists. This is the physically meaningful
    statement — the causal structure cannot be "unwound."
    Corollary of `growth_irreversible` (the stronger cardinality result). -/
theorem growth_no_causal_retraction (G : Core.DynamicGraph) (t : ℕ)
    [Fintype (G.V t)] [Fintype (G.V (t + 1))] :
    ¬ ∃ (π : G.V (t + 1) ↪ G.V t),
      ∀ u v, G.E (t + 1) u v → G.E t (π u) (π v) := by
  intro ⟨π, _⟩
  exact growth_irreversible G t ⟨π, trivial⟩

end HeytingLean.FractalUniverse.NucleusConnection
