import HeytingLean.Topology.Knot.VirtualInvariantBridge

/-!
# Topology Virtual Invariant Bridge Sanity
-/

namespace HeytingLean.Tests.Topology

open HeytingLean.Topology.Knot

#check bracketSignature
#check conwaySignature
#check SignedVirtualClass
#check virtual_class_respects_bracket_signature
#check virtual_class_respects_bracket_signature_r1_pos
#check virtual_class_respects_bracket_signature_r3_of_skeinStep_eq
#check virtual_class_respects_bracket_signature_r3_of_tl3_bridge_endpoints
#check virtual_class_respects_bracket_signature_r3_of_bridge_witness
#check virtual_class_respects_bracket_signature_r3_of_two_level_bridge_witness
#check virtual_class_respects_conway_signature

example {g g' : PDGraph} {x u : Nat}
    (h : Reidemeister.r2Add g x u = .ok g') :
    bracketSignature g' = bracketSignature g := by
  exact virtual_class_respects_bracket_signature h

example {g g' : PDGraph} {x : Nat}
    (h : Reidemeister.r1Add g x .pos = .ok g') :
    bracketSignature g' =
      (do
        let b ← bracketSignature g
        return (-(Kauffman.AML ^ 3 : Kauffman.PolyML)) * b) := by
  exact virtual_class_respects_bracket_signature_r1_pos h

example {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hStepEq : Kauffman.r3SkeinStep gL = Kauffman.r3SkeinStep gR) :
    bracketSignature gL = bracketSignature gR := by
  exact virtual_class_respects_bracket_signature_r3_of_skeinStep_eq hLeft hRight hStepEq

example {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftTL :
      Kauffman.r3SkeinStep gL =
        Kauffman.TL3Context.evalTL3Expr fuel g x u w Kauffman.R3.tlWordLeft)
    (hRightTL :
      Kauffman.r3SkeinStep gR =
        Kauffman.TL3Context.evalTL3Expr fuel g x u w Kauffman.R3.tlWordRight) :
    bracketSignature gL = bracketSignature gR := by
  exact virtual_class_respects_bracket_signature_r3_of_tl3_bridge_endpoints
    hLeft hRight hLeftTL hRightTL

example {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBridge : Kauffman.R3SkeinBridgeWitness g gL gR x u w) :
    bracketSignature gL = bracketSignature gR := by
  exact virtual_class_respects_bracket_signature_r3_of_bridge_witness
    hLeft hRight hBridge

example {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwo : Kauffman.R3TwoLevelBridgeWitness g x u w) :
    bracketSignature gL = bracketSignature gR := by
  exact virtual_class_respects_bracket_signature_r3_of_two_level_bridge_witness
    hLeft hRight hTwo

example {fuel : Nat} {s : Kauffman.SignedPDGraph}
    (hClass : SignedVirtualClass s)
    (hn : s.graph.n ≠ 0)
    (hSign : s.sign[s.graph.n - 1]! = .pos) :
    Kauffman.SignedPDGraph.conwayWithFuel (fuel + 1) s =
      (do
        let s0 ← Kauffman.SignedPDGraph.lZeroLast s
        let p0 ← Kauffman.SignedPDGraph.conwayWithFuel fuel s0
        let sm ← Kauffman.SignedPDGraph.lMinusLast s
        let pm ← Kauffman.SignedPDGraph.conwayWithFuel fuel sm
        pure (pm + Kauffman.z * p0)) := by
  exact virtual_class_respects_conway_signature hClass hn hSign

end HeytingLean.Tests.Topology
