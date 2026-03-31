import HeytingLean.Genesis

/-!
# Genesis Kauffman Transport Interface Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis

#check CoGame.reRoot
#check TransportNodeMap
#check LocalMoveTransport
#check transport_respects_local_move
#check transport_bisim_invariant

def unitTransportNodeMap : TransportNodeMap Unit OmegaGraph CoGame.Life where
  toMemNode _ := Omega
  toCoNode _ := CoGame.Life.root
  mem_to_co_edge := by
    intro a b hab
    constructor <;> simp [CoGame.Life]

def unitTransport : LocalMoveTransport Unit OmegaGraph CoGame.Life where
  move _ _ := True
  nodeMap := unitTransportNodeMap
  move_preserves_memBisim := by
    intro a b hmove
    exact MemGraph.bisim_refl (G := OmegaGraph) (x := Omega)
  move_preserves_coBisim := by
    intro a b hmove
    exact CoGame.bisim_refl (CoGame.reRoot CoGame.Life CoGame.Life.root)

example :
    MemGraph.Bisim OmegaGraph (unitTransport.nodeMap.toMemNode ()) (unitTransport.nodeMap.toMemNode ()) ∧
      CoGame.Bisim
        (CoGame.reRoot CoGame.Life (unitTransport.nodeMap.toCoNode ()))
        (CoGame.reRoot CoGame.Life (unitTransport.nodeMap.toCoNode ())) := by
  exact transport_respects_local_move unitTransport (a := ()) (b := ()) trivial

example :
    MemGraph.Bisim OmegaGraph (unitTransport.nodeMap.toMemNode ()) (unitTransport.nodeMap.toMemNode ()) ∧
      CoGame.Bisim
        (CoGame.reRoot CoGame.Life (unitTransport.nodeMap.toCoNode ()))
        (CoGame.reRoot CoGame.Life (unitTransport.nodeMap.toCoNode ())) := by
  exact transport_bisim_invariant unitTransport
    (a := ()) (b := ()) (Relation.ReflTransGen.single trivial)

end HeytingLean.Tests.Genesis
