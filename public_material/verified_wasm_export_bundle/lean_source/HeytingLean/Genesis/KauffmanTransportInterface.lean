import HeytingLean.Genesis.KnotSetGraph
import Mathlib.Logic.Relation

/-!
# Genesis.KauffmanTransportInterface

Phase-K1 interface layer for transporting knot/local-rewrite objects into:
- membership-graph semantics (`MemGraph`), and
- loopy co-game semantics (`CoGame`).

This file is intentionally interface-first: it introduces no topology-specific
Reidemeister details and no new axioms.
-/

namespace HeytingLean.Genesis

universe u v w

namespace CoGame

/-- Re-root a co-game at a chosen node while preserving the transition structure. -/
def reRoot (G : CoGame.{u}) (r : G.Node) : CoGame where
  Node := G.Node
  root := r
  leftSucc := G.leftSucc
  rightSucc := G.rightSucc

@[simp] theorem reRoot_root (G : CoGame.{u}) (r : G.Node) :
    (reRoot G r).root = r := rfl

@[simp] theorem reRoot_leftSucc (G : CoGame.{u}) (r x : G.Node) :
    (reRoot G r).leftSucc x = G.leftSucc x := rfl

@[simp] theorem reRoot_rightSucc (G : CoGame.{u}) (r x : G.Node) :
    (reRoot G r).rightSucc x = G.rightSucc x := rfl

end CoGame

/--
Transport map from an external rewrite-domain `α` into both semantic carriers:
membership-graph nodes and co-game nodes.
-/
structure TransportNodeMap (α : Type u) (M : MemGraph.{v}) (C : CoGame.{w}) where
  toMemNode : α → M.Node
  toCoNode : α → C.Node
  /--
  Compatibility witness: a transported membership edge induces both left and right
  co-game successor membership. This keeps the interface symmetric by default.
  -/
  mem_to_co_edge :
    ∀ {a b : α}, M.mem (toMemNode a) (toMemNode b) →
      toCoNode a ∈ C.leftSucc (toCoNode b) ∧ toCoNode a ∈ C.rightSucc (toCoNode b)

/--
Interface bundle for a local rewrite relation plus the semantic transport contracts
needed by closure proofs.
-/
structure LocalMoveTransport (α : Type u) (M : MemGraph.{v}) (C : CoGame.{w}) where
  move : α → α → Prop
  nodeMap : TransportNodeMap α M C
  move_preserves_memBisim :
    ∀ {a b : α}, move a b →
      MemGraph.Bisim M (nodeMap.toMemNode a) (nodeMap.toMemNode b)
  move_preserves_coBisim :
    ∀ {a b : α}, move a b →
      CoGame.Bisim (CoGame.reRoot C (nodeMap.toCoNode a))
        (CoGame.reRoot C (nodeMap.toCoNode b))

/--
One-step local move preservation: the transport produces bisimilar semantic states
in both the membership and co-game views.
-/
theorem transport_respects_local_move
    {α : Type u} {M : MemGraph.{v}} {C : CoGame.{w}}
    (T : LocalMoveTransport α M C) {a b : α} (h : T.move a b) :
    MemGraph.Bisim M (T.nodeMap.toMemNode a) (T.nodeMap.toMemNode b) ∧
      CoGame.Bisim (CoGame.reRoot C (T.nodeMap.toCoNode a))
        (CoGame.reRoot C (T.nodeMap.toCoNode b)) := by
  exact ⟨T.move_preserves_memBisim h, T.move_preserves_coBisim h⟩

/--
Reflexive-transitive local rewrite invariance: transport remains bisimulation-stable
along any finite chain of local rewrites.
-/
theorem transport_bisim_invariant
    {α : Type u} {M : MemGraph.{v}} {C : CoGame.{w}}
    (T : LocalMoveTransport α M C) {a b : α}
    (h : Relation.ReflTransGen T.move a b) :
    MemGraph.Bisim M (T.nodeMap.toMemNode a) (T.nodeMap.toMemNode b) ∧
      CoGame.Bisim (CoGame.reRoot C (T.nodeMap.toCoNode a))
        (CoGame.reRoot C (T.nodeMap.toCoNode b)) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl x =>
      refine ⟨?_, ?_⟩
      · exact MemGraph.bisim_refl (G := M) (x := T.nodeMap.toMemNode x)
      · exact CoGame.bisim_refl (CoGame.reRoot C (T.nodeMap.toCoNode x))
  | single hab =>
      exact transport_respects_local_move T hab
  | trans hab hbc ihab ihbc =>
      rcases ihab with ⟨hMemAB, hCoAB⟩
      rcases ihbc with ⟨hMemBC, hCoBC⟩
      refine ⟨?_, ?_⟩
      · exact MemGraph.bisim_trans (G := M) hMemAB hMemBC
      · exact CoGame.bisim_trans hCoAB hCoBC

end HeytingLean.Genesis
