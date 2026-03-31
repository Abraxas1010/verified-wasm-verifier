import HeytingLean.Genesis.KauffmanTransportInterface
import HeytingLean.Topology.Knot.Reidemeister
import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR3

/-!
# Knot.VirtualTransport

Phase-K2 bridge from executable Reidemeister local moves into the K1 virtual
transport interface.

This layer is intentionally conservative:
- it provides a concrete local-move relation over `PDGraph`,
- instantiates the K1 transport contracts, and
- proves R1/R2 preservation of a transport-ready virtual class (`validate = ok`).
-/

namespace HeytingLean
namespace Topology
namespace Knot

open HeytingLean.Genesis
open Reidemeister

/-- Minimal transport-ready virtual class for executable knot states. -/
def VirtualClass (g : PDGraph) : Prop :=
  PDGraph.validate g = .ok ()

/-- Local Reidemeister-style move relation used by the transport interface. -/
inductive LocalMove : PDGraph → PDGraph → Prop
  | r1 {g g' : PDGraph} {x : Nat} {kind : CurlKind}
      (h : Reidemeister.r1Add g x kind = .ok g') : LocalMove g g'
  | r2 {g g' : PDGraph} {x u : Nat}
      (h : Reidemeister.r2Add g x u = .ok g') : LocalMove g g'

/--
Concrete K1 transport map used for K2 closure proofs.
`PDGraph` states are projected to canonical virtual anchors (`Omega`, `Life.root`).
-/
def omegaLifeNodeMap : TransportNodeMap PDGraph OmegaGraph CoGame.Life where
  toMemNode _ := Omega
  toCoNode _ := CoGame.Life.root
  mem_to_co_edge := by
    intro a b hab
    constructor
    · change () = ()
      rfl
    · change () = ()
      rfl

/-- K1 transport instantiation for the Reidemeister local-move relation. -/
def omegaLifeTransport : LocalMoveTransport PDGraph OmegaGraph CoGame.Life where
  move := LocalMove
  nodeMap := omegaLifeNodeMap
  move_preserves_memBisim := by
    intro a b hmove
    exact MemGraph.bisim_refl (G := OmegaGraph) (x := Omega)
  move_preserves_coBisim := by
    intro a b hmove
    exact CoGame.bisim_refl (CoGame.reRoot CoGame.Life CoGame.Life.root)

theorem transport_localMove_preserves_virtual_bisim
    {g g' : PDGraph} (h : LocalMove g g') :
    MemGraph.Bisim OmegaGraph (omegaLifeNodeMap.toMemNode g) (omegaLifeNodeMap.toMemNode g') ∧
      CoGame.Bisim (CoGame.reRoot CoGame.Life (omegaLifeNodeMap.toCoNode g))
        (CoGame.reRoot CoGame.Life (omegaLifeNodeMap.toCoNode g')) := by
  exact transport_respects_local_move omegaLifeTransport h

/--
R1 closure theorem (K2 gate): successful `r1Add` preserves the virtual class.
-/
theorem transport_R1_preserves_virtual_class
    {g g' : PDGraph} {x : Nat} {kind : CurlKind}
    (h : Reidemeister.r1Add g x kind = .ok g') :
    VirtualClass g' := by
  cases hvg' : PDGraph.validate g' with
  | error e =>
      have hrem :=
        Reidemeister.r1RemoveLast_of_r1Add_ok
          (g := g) (g' := g') (x := x) (kind := kind) h
      have herr : Reidemeister.r1RemoveLast g' kind = .error e := by
        simp [Reidemeister.r1RemoveLast, hvg']
      rw [herr] at hrem
      cases hrem
  | ok u =>
      cases u
      simpa [VirtualClass] using hvg'

/--
R2 closure theorem (K2 gate): successful `r2Add` preserves the virtual class.
-/
theorem transport_R2_preserves_virtual_class
    {g g' : PDGraph} {x u : Nat}
    (h : Reidemeister.r2Add g x u = .ok g') :
    VirtualClass g' := by
  cases hvg' : PDGraph.validate g' with
  | error e =>
      have hrem :=
        Reidemeister.r2RemoveLast_of_r2Add_ok
          (g := g) (g' := g') (x := x) (u := u) h
      have herr : Reidemeister.r2RemoveLast g' = .error e := by
        simp [Reidemeister.r2RemoveLast, hvg']
      rw [herr] at hrem
      cases hrem
  | ok v =>
      cases v
      simpa [VirtualClass] using hvg'

/--
R3-left closure theorem: successful braid-left constructor output is transport-valid.
-/
theorem transport_R3_left_preserves_virtual_class
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    VirtualClass gL := by
  have hValid : PDGraph.Valid gL :=
    Kauffman.r3BraidLeft_valid (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  simpa [VirtualClass] using PDGraph.validate_eq_ok_of_valid hValid

/--
R3-right closure theorem: successful braid-right constructor output is transport-valid.
-/
theorem transport_R3_right_preserves_virtual_class
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    VirtualClass gR := by
  have hValid : PDGraph.Valid gR :=
    Kauffman.r3BraidRight_valid (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  simpa [VirtualClass] using PDGraph.validate_eq_ok_of_valid hValid

/--
Interface witness for R3 transport pairs:
both braid endpoints plus explicit class-equivalence witness.
-/
structure R3TransportPair (g : PDGraph) (x u w : Nat) where
  left : PDGraph
  right : PDGraph
  left_ok : Reidemeister.r3BraidLeft g x u w = .ok left
  right_ok : Reidemeister.r3BraidRight g x u w = .ok right
  class_equiv : VirtualClass left ↔ VirtualClass right

/--
Canonical constructor for an R3 transport pair from executable braid endpoints.
-/
def mkR3TransportPair
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR) :
    R3TransportPair g x u w where
  left := gL
  right := gR
  left_ok := hLeft
  right_ok := hRight
  class_equiv := by
    constructor <;> intro _
    · exact transport_R3_right_preserves_virtual_class hRight
    · exact transport_R3_left_preserves_virtual_class hLeft

/-- Transport compatibility theorem over the dedicated R3 transport-pair interface. -/
theorem transport_R3_pair_preserves_virtual_class
    {g : PDGraph} {x u w : Nat}
    (pair : R3TransportPair g x u w) :
    VirtualClass pair.left ∧ VirtualClass pair.right := by
  exact ⟨transport_R3_left_preserves_virtual_class pair.left_ok,
    transport_R3_right_preserves_virtual_class pair.right_ok⟩

/--
The R3 pair interface stores a class-equivalence witness; this theorem re-exposes it.
-/
theorem transport_R3_pair_virtual_class_equiv
    {g : PDGraph} {x u w : Nat}
    (pair : R3TransportPair g x u w) :
    VirtualClass pair.left ↔ VirtualClass pair.right :=
  pair.class_equiv

/--
R3 pair transport is bisimulation-stable under the K1 node map.
-/
theorem transport_R3_pair_preserves_virtual_bisim
    {g : PDGraph} {x u w : Nat}
    (pair : R3TransportPair g x u w) :
    MemGraph.Bisim OmegaGraph
      (omegaLifeNodeMap.toMemNode pair.left)
      (omegaLifeNodeMap.toMemNode pair.right) ∧
      CoGame.Bisim
        (CoGame.reRoot CoGame.Life (omegaLifeNodeMap.toCoNode pair.left))
        (CoGame.reRoot CoGame.Life (omegaLifeNodeMap.toCoNode pair.right)) := by
  refine ⟨?_, ?_⟩
  · exact MemGraph.bisim_refl (G := OmegaGraph) (x := omegaLifeNodeMap.toMemNode pair.left)
  · exact CoGame.bisim_refl
      (CoGame.reRoot CoGame.Life (omegaLifeNodeMap.toCoNode pair.left))

end Knot
end Topology
end HeytingLean
