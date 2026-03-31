import Mathlib.Data.Fintype.Card

/-!
# Dynamic Graph Structure

Formalizes the dynamic oriented graph G(t, ℓ) from Veselov's
"Fractal Universe" paper (Section 2.1). Vertices are elementary
spacetime cells, directed edges are causal relations, and the graph
grows monotonically with discrete time parameter t.
-/

namespace HeytingLean.FractalUniverse.Core

/-- A dynamic oriented graph G(t) modeling an evolving causal structure.
    Source: Veselov Section 2.1. -/
structure DynamicGraph where
  /-- Vertex type at each discrete time step. -/
  V : ℕ → Type
  /-- Directed edge relation (causal order) at time `t`. -/
  E : (t : ℕ) → V t → V t → Prop
  /-- Causal order is irreflexive (no self-causation). -/
  causal_irrefl : ∀ t v, ¬ E t v v
  /-- Causal order is transitive. -/
  causal_trans : ∀ t u v w, E t u v → E t v w → E t u w
  /-- Growth map: injection from V(t) into V(t+1). -/
  growth : (t : ℕ) → V t → V (t + 1)
  /-- Growth is injective (vertices are not identified). -/
  growth_injective : ∀ t, Function.Injective (growth t)
  /-- Growth preserves the causal order. -/
  growth_preserves_edges : ∀ t u v, E t u v → E (t + 1) (growth t u) (growth t v)
  /-- At each step, at least one genuinely new vertex appears. -/
  has_new_vertices : ∀ t, ∃ v : V (t + 1), ∀ u : V t, growth t u ≠ v

/-- Vertex count is strictly increasing at each time step.
    Proof: the growth map is an injection that is not surjective
    (by `has_new_vertices`), so the domain is strictly smaller. -/
theorem monotone_vertex_count (G : DynamicGraph) (t : ℕ)
    [Fintype (G.V t)] [Fintype (G.V (t + 1))] :
    Fintype.card (G.V t) < Fintype.card (G.V (t + 1)) := by
  obtain ⟨v, hv⟩ := G.has_new_vertices t
  exact Fintype.card_lt_of_injective_of_notMem (G.growth t)
    (G.growth_injective t) (by simpa [Set.mem_range] using fun u => hv u)

/-- The causal order at time t embeds into time t+1 via the growth map. -/
theorem causal_order_extends (G : DynamicGraph) (t : ℕ) (u v : G.V t)
    (h : G.E t u v) : G.E (t + 1) (G.growth t u) (G.growth t v) :=
  G.growth_preserves_edges t u v h

/-- Composition of growth maps: from time `t` to time `t + k`. -/
def growthN (G : DynamicGraph) (t : ℕ) : (k : ℕ) → G.V t → G.V (t + k)
  | 0 => fun v => by rw [Nat.add_zero]; exact v
  | k + 1 => fun v => by
    rw [Nat.add_succ]
    exact G.growth (t + k) (growthN G t k v)

end HeytingLean.FractalUniverse.Core
