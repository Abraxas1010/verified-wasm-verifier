import HeytingLean.PerspectivalPlenum.VirtualKnotTransportBridge

/-!
# Perspectival Plenum Virtual Knot Transport Bridge Sanity
-/

namespace HeytingLean.Tests.PerspectivalPlenum

open HeytingLean.PerspectivalPlenum.VirtualKnotTransportBridge

#check virtualKnotObstructionClass
#check virtual_transport_obstruction_hook_r1
#check virtual_transport_obstruction_hook_r2
#check virtual_transport_obstruction_hook_r3_left
#check virtual_transport_obstruction_hook_r3_right
#check virtual_transport_obstruction_hook_r3_pair
#check virtual_transport_bracket_hook_r2
#check virtual_transport_bracket_hook_r3_of_skeinStep_eq
#check virtual_transport_bracket_hook_r3_of_tl3_bridge_endpoints
#check virtual_transport_bracket_hook_r3_of_bridge_witness
#check virtual_transport_bracket_hook_r3_of_two_level_bridge_witness

example {g g' : HeytingLean.Topology.Knot.PDGraph}
    {x : Nat} {kind : HeytingLean.Topology.Knot.Reidemeister.CurlKind}
    (h : HeytingLean.Topology.Knot.Reidemeister.r1Add g x kind = .ok g') :
    virtualKnotObstructionClass g' =
      HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.none := by
  exact virtual_transport_obstruction_hook_r1 h

example {g g' : HeytingLean.Topology.Knot.PDGraph}
    {x u : Nat}
    (h : HeytingLean.Topology.Knot.Reidemeister.r2Add g x u = .ok g') :
    virtualKnotObstructionClass g' =
      HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.none := by
  exact virtual_transport_obstruction_hook_r2 h

example {g g' : HeytingLean.Topology.Knot.PDGraph}
    {x u : Nat}
    (h : HeytingLean.Topology.Knot.Reidemeister.r2Add g x u = .ok g') :
    HeytingLean.Topology.Knot.bracketSignature g' =
      HeytingLean.Topology.Knot.bracketSignature g := by
  exact virtual_transport_bracket_hook_r2 h

example {g gL : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (h : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL) :
    virtualKnotObstructionClass gL =
      HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.none := by
  exact virtual_transport_obstruction_hook_r3_left h

example {g gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (h : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR) :
    virtualKnotObstructionClass gR =
      HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.none := by
  exact virtual_transport_obstruction_hook_r3_right h

example {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hL : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hR : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR) :
    let pair := HeytingLean.Topology.Knot.mkR3TransportPair (g := g) (x := x) (u := u) (w := w) hL hR
    virtualKnotObstructionClass pair.left =
      HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.none ∧
      virtualKnotObstructionClass pair.right =
        HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.none := by
  intro pair
  exact virtual_transport_obstruction_hook_r3_pair pair

example {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hStepEq : HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gL =
      HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gR) :
    HeytingLean.Topology.Knot.bracketSignature gL =
    HeytingLean.Topology.Knot.bracketSignature gR := by
  exact virtual_transport_bracket_hook_r3_of_skeinStep_eq hLeft hRight hStepEq

example {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w fuel : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftTL :
      HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gL =
        HeytingLean.Topology.Knot.Kauffman.TL3Context.evalTL3Expr fuel g x u w
          HeytingLean.Topology.Knot.Kauffman.R3.tlWordLeft)
    (hRightTL :
      HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gR =
        HeytingLean.Topology.Knot.Kauffman.TL3Context.evalTL3Expr fuel g x u w
          HeytingLean.Topology.Knot.Kauffman.R3.tlWordRight) :
    HeytingLean.Topology.Knot.bracketSignature gL =
      HeytingLean.Topology.Knot.bracketSignature gR := by
  exact virtual_transport_bracket_hook_r3_of_tl3_bridge_endpoints
    hLeft hRight hLeftTL hRightTL

example {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBridge :
      HeytingLean.Topology.Knot.Kauffman.R3SkeinBridgeWitness g gL gR x u w) :
    HeytingLean.Topology.Knot.bracketSignature gL =
      HeytingLean.Topology.Knot.bracketSignature gR := by
  exact virtual_transport_bracket_hook_r3_of_bridge_witness
    hLeft hRight hBridge

example {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwo :
      HeytingLean.Topology.Knot.Kauffman.R3TwoLevelBridgeWitness g x u w) :
    HeytingLean.Topology.Knot.bracketSignature gL =
      HeytingLean.Topology.Knot.bracketSignature gR := by
  exact virtual_transport_bracket_hook_r3_of_two_level_bridge_witness
    hLeft hRight hTwo

end HeytingLean.Tests.PerspectivalPlenum
