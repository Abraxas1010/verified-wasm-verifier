import HeytingLean.CategoryTheory.Polynomial.Basic

/-!
# Polynomial Architecture Graph Constraints

Typed graph constraints for architecture candidates represented over polynomial
modules. This provides a lightweight gate before expensive training/search.
-/

namespace HeytingLean.CategoryTheory.Polynomial

open _root_.CategoryTheory.Polynomial

universe u

/-- Port classes used to enforce compositional compatibility. -/
inductive ArchPortKind
  | input
  | latent
  | output
  | loss
deriving DecidableEq, Repr

/-- A candidate architecture node with polynomial payload and typed IO ports. -/
structure ArchNode where
  poly : Poly.{u, u}
  inPort : ArchPortKind
  outPort : ArchPortKind

namespace ArchNode

/-- Port-compatibility relation used by composition checks. -/
def compatible (a b : ArchNode) : Bool :=
  decide (a.outPort = b.inPort)

@[simp] theorem compatible_eq_true_iff (a b : ArchNode) :
    compatible a b = true ↔ a.outPort = b.inPort := by
  unfold compatible
  exact decide_eq_true_iff

@[simp] theorem compatible_eq_false_iff (a b : ArchNode) :
    compatible a b = false ↔ a.outPort ≠ b.inPort := by
  unfold compatible
  exact decide_eq_false_iff_not

end ArchNode

/-- Edge in an architecture candidate graph. -/
structure ArchEdge where
  src : Nat
  dst : Nat
deriving DecidableEq, Repr

/-- Candidate architecture graph with indexed nodes and directed edges. -/
structure ArchCandidate where
  nodes : Array ArchNode
  edges : Array ArchEdge

/-- Edge index bounds check. -/
def edgeWithinBounds (nodes : Array ArchNode) (e : ArchEdge) : Bool :=
  e.src < nodes.size && e.dst < nodes.size

/-- Edge compatibility check (source output port must match target input port). -/
def edgePortsMatch (nodes : Array ArchNode) (e : ArchEdge) : Bool :=
  match nodes[e.src]?, nodes[e.dst]? with
  | some src, some dst => ArchNode.compatible src dst
  | _, _ => false

/-- Ban self-loops in the constrained composition graph. -/
def edgeNoSelfLoop (e : ArchEdge) : Bool :=
  decide (e.src ≠ e.dst)

/-- Full validity check for a single edge. -/
def validEdge (nodes : Array ArchNode) (e : ArchEdge) : Bool :=
  edgeWithinBounds nodes e && edgePortsMatch nodes e && edgeNoSelfLoop e

/-- Full candidate validity check used for pre-training rejection. -/
def validCandidate (c : ArchCandidate) : Bool :=
  c.edges.all (fun e => validEdge c.nodes e)

end HeytingLean.CategoryTheory.Polynomial
