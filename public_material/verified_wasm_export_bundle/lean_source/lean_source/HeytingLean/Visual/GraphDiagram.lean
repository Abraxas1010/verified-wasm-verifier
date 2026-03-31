import HeytingLean.Bridges.Graph

/-
# Visual.GraphDiagram

A tiny, purely semantic path language over the graph bridge.  Diagrams are
built from identities, primitive adjacency edges, and composition, and they
are evaluated into the adjacency relation itself.

This provides a minimal Lean-level representation of graph/flow diagrams that
can be used as a backend for visualization and for stating reachability-style
properties without introducing any I/O dependencies.
-/

namespace HeytingLean
namespace Visual
namespace Graph

open HeytingLean.Bridges
open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-- Simple path diagrams in the graph bridge `Graph.Model`. -/
inductive Diagram (M : Bridges.Graph.Model α) :
    M.Carrier → M.Carrier → Type u where
  | id (x : M.Carrier) :
      Diagram M x x
  | edge {x y : M.Carrier} (h : M.adjacency x y) :
      Diagram M x y
  | comp {x y z : M.Carrier} :
      Diagram M x y → Diagram M y z → Diagram M x z

namespace Diagram

variable {M : Bridges.Graph.Model α}

/-- Interpret a graph diagram as an adjacency fact (`x ≤ y`) in the graph
bridge. -/
def eval {x y : M.Carrier} : Diagram M x y → M.adjacency x y
  | id _ => M.adjacency_refl _
  | edge h => h
  | comp f g => M.adjacency_trans (eval f) (eval g)

@[simp] lemma eval_id (x : M.Carrier) :
    eval (Diagram.id (M := M) x) = M.adjacency_refl x :=
  rfl

@[simp] lemma eval_edge {x y : M.Carrier} (h : M.adjacency x y) :
    eval (Diagram.edge (M := M) (x := x) (y := y) h) = h :=
  rfl

@[simp] lemma eval_comp {x y z : M.Carrier}
    (f : Diagram M x y) (g : Diagram M y z) :
    eval (Diagram.comp f g) =
      M.adjacency_trans (eval f) (eval g) :=
  rfl

end Diagram

end Graph
end Visual
end HeytingLean
