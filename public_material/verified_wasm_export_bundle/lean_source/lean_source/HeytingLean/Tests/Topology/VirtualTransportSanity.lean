import HeytingLean.Topology.Knot.VirtualTransport

/-!
# Topology Virtual Transport Sanity
-/

namespace HeytingLean.Tests.Topology

open HeytingLean.Topology.Knot
open HeytingLean.Genesis

#check VirtualClass
#check LocalMove
#check omegaLifeNodeMap
#check omegaLifeTransport
#check transport_localMove_preserves_virtual_bisim
#check transport_R1_preserves_virtual_class
#check transport_R2_preserves_virtual_class
#check transport_R3_left_preserves_virtual_class
#check transport_R3_right_preserves_virtual_class
#check R3TransportPair
#check mkR3TransportPair
#check transport_R3_pair_preserves_virtual_class
#check transport_R3_pair_virtual_class_equiv
#check transport_R3_pair_preserves_virtual_bisim

example {g g' : PDGraph} {x : Nat} {kind : Reidemeister.CurlKind}
    (h : Reidemeister.r1Add g x kind = .ok g') :
    VirtualClass g' := by
  exact transport_R1_preserves_virtual_class h

example {g g' : PDGraph} {x u : Nat}
    (h : Reidemeister.r2Add g x u = .ok g') :
    VirtualClass g' := by
  exact transport_R2_preserves_virtual_class h

example {g g' : PDGraph} (h : LocalMove g g') :
    MemGraph.Bisim OmegaGraph (omegaLifeNodeMap.toMemNode g) (omegaLifeNodeMap.toMemNode g') ∧
      CoGame.Bisim (CoGame.reRoot CoGame.Life (omegaLifeNodeMap.toCoNode g))
        (CoGame.reRoot CoGame.Life (omegaLifeNodeMap.toCoNode g')) := by
  exact transport_localMove_preserves_virtual_bisim h

example {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    VirtualClass gL := by
  exact transport_R3_left_preserves_virtual_class h

example {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    VirtualClass gR := by
  exact transport_R3_right_preserves_virtual_class h

example {g gL gR : PDGraph} {x u w : Nat}
    (hL : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hR : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let pair := mkR3TransportPair (g := g) (x := x) (u := u) (w := w) hL hR
    VirtualClass pair.left ∧ VirtualClass pair.right := by
  intro pair
  exact transport_R3_pair_preserves_virtual_class pair

end HeytingLean.Tests.Topology
