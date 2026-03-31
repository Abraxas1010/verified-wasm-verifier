import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# MirandaDynamics.Topology: a β₁ proxy via graph cycle rank

The Miranda billiards paper relates “topological complexity” of an obstacle layout to computational
power.  Recomputing billiard-table homology in full generality is outside the current scope of this
repo, but we can mechanize a clean **graph-theoretic proxy** for first Betti number:

For a (finite) connected graph `G`, define the cycle rank

`cycleRank(G) := |E| + 1 - |V|`.

For a tree this is `0`, and for connected graphs it is always well-defined in the sense that
`|V| ≤ |E| + 1` (a standard bound mechanized in mathlib).

This is a mathematically honest “β₁ proxy” for 1-dimensional CW-complexes.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Topology

open SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

/-- Cycle rank `|E| + 1 - |V|` (a β₁ proxy) using `Nat.card` for finite types. -/
noncomputable def cycleRank : Nat :=
  Nat.card G.edgeSet + 1 - Nat.card V

theorem connected_card_vert_le_card_edgeSet_add_one [Finite V] (h : G.Connected) :
    Nat.card V ≤ Nat.card G.edgeSet + 1 :=
  h.card_vert_le_card_edgeSet_add_one

theorem cycleRank_eq_zero_of_isTree [Finite V] (h : G.IsTree) : cycleRank G = 0 := by
  -- For trees, mathlib gives `|E|+1 = |V|`.
  have hcard : Nat.card G.edgeSet + 1 = Nat.card V :=
    (SimpleGraph.isTree_iff_connected_and_card (G := G)).1 h |>.2
  unfold cycleRank
  -- `(|E|+1) - |V| = 0`.
  rw [hcard]
  simp

end Topology
end MirandaDynamics
end HeytingLean
