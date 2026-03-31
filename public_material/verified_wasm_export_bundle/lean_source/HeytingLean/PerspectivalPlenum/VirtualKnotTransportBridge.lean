import HeytingLean.PerspectivalPlenum.CechObstruction
import HeytingLean.Topology.Knot.VirtualTransport
import HeytingLean.Topology.Knot.VirtualInvariantBridge

/-!
# PerspectivalPlenum.VirtualKnotTransportBridge

Bridge from knot-side virtual transport classes into plenum obstruction classes.
-/

namespace HeytingLean
namespace PerspectivalPlenum
namespace VirtualKnotTransportBridge

open ContextualityEngine
open scoped Classical

/-- Obstruction classifier for transported knot states. -/
noncomputable def virtualKnotObstructionClass
    (g : HeytingLean.Topology.Knot.PDGraph) : CechObstructionClass :=
  by
    classical
    exact if HeytingLean.Topology.Knot.VirtualClass g then .none else .h1_overlap_incompatibility

@[simp] theorem virtualKnotObstructionClass_of_virtual
    {g : HeytingLean.Topology.Knot.PDGraph}
    (h : HeytingLean.Topology.Knot.VirtualClass g) :
    virtualKnotObstructionClass g = .none := by
  classical
  simp [virtualKnotObstructionClass, h]

/--
Plenum hook for transported R1 moves: successful transport lands in the no-obstruction
class for the transported knot state.
-/
theorem virtual_transport_obstruction_hook_r1
    {g g' : HeytingLean.Topology.Knot.PDGraph}
    {x : Nat} {kind : HeytingLean.Topology.Knot.Reidemeister.CurlKind}
    (hMove : HeytingLean.Topology.Knot.Reidemeister.r1Add g x kind = .ok g') :
    virtualKnotObstructionClass g' = .none := by
  exact virtualKnotObstructionClass_of_virtual
    (HeytingLean.Topology.Knot.transport_R1_preserves_virtual_class hMove)

/--
Plenum hook for transported R2 moves: successful transport lands in the no-obstruction
class for the transported knot state.
-/
theorem virtual_transport_obstruction_hook_r2
    {g g' : HeytingLean.Topology.Knot.PDGraph}
    {x u : Nat}
    (hMove : HeytingLean.Topology.Knot.Reidemeister.r2Add g x u = .ok g') :
    virtualKnotObstructionClass g' = .none := by
  exact virtualKnotObstructionClass_of_virtual
    (HeytingLean.Topology.Knot.transport_R2_preserves_virtual_class hMove)

/--
Plenum hook for transported R3-left braid outputs: successful transport lands in
the no-obstruction class for the left braid endpoint.
-/
theorem virtual_transport_obstruction_hook_r3_left
    {g gL : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hMove : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL) :
    virtualKnotObstructionClass gL = .none := by
  exact virtualKnotObstructionClass_of_virtual
    (HeytingLean.Topology.Knot.transport_R3_left_preserves_virtual_class hMove)

/--
Plenum hook for transported R3-right braid outputs: successful transport lands in
the no-obstruction class for the right braid endpoint.
-/
theorem virtual_transport_obstruction_hook_r3_right
    {g gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hMove : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR) :
    virtualKnotObstructionClass gR = .none := by
  exact virtualKnotObstructionClass_of_virtual
    (HeytingLean.Topology.Knot.transport_R3_right_preserves_virtual_class hMove)

/--
Plenum hook for the dedicated R3 transport-pair interface.
-/
theorem virtual_transport_obstruction_hook_r3_pair
    {g : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (pair : HeytingLean.Topology.Knot.R3TransportPair g x u w) :
    virtualKnotObstructionClass pair.left = .none ∧
      virtualKnotObstructionClass pair.right = .none := by
  exact ⟨virtual_transport_obstruction_hook_r3_left pair.left_ok,
    virtual_transport_obstruction_hook_r3_right pair.right_ok⟩

/-- Bridge hook exposing transported R2 bracket-signature invariance to plenum tooling. -/
theorem virtual_transport_bracket_hook_r2
    {g g' : HeytingLean.Topology.Knot.PDGraph}
    {x u : Nat}
    (hMove : HeytingLean.Topology.Knot.Reidemeister.r2Add g x u = .ok g') :
    HeytingLean.Topology.Knot.bracketSignature g' =
      HeytingLean.Topology.Knot.bracketSignature g := by
  exact HeytingLean.Topology.Knot.virtual_class_respects_bracket_signature hMove

/--
R3 bracket hook (conditional, no axioms): if left/right braid endpoints agree at
the one-step skein level, their bracket signatures agree.
-/
theorem virtual_transport_bracket_hook_r3_of_skeinStep_eq
    {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hStepEq : HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gL =
      HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gR) :
    HeytingLean.Topology.Knot.bracketSignature gL =
      HeytingLean.Topology.Knot.bracketSignature gR := by
  exact HeytingLean.Topology.Knot.virtual_class_respects_bracket_signature_r3_of_skeinStep_eq
    hLeft hRight hStepEq

/--
R3 bracket hook via TL3 bridge correspondences (endpoint form).
-/
theorem virtual_transport_bracket_hook_r3_of_tl3_bridge_endpoints
    {g gL gR : HeytingLean.Topology.Knot.PDGraph}
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
  exact HeytingLean.Topology.Knot.virtual_class_respects_bracket_signature_r3_of_tl3_bridge_endpoints
    hLeft hRight hLeftTL hRightTL

/--
R3 bracket hook via the unified bridge witness.

This accepts either route encoded by
`HeytingLean.Topology.Knot.Kauffman.R3SkeinBridgeWitness`.
-/
theorem virtual_transport_bracket_hook_r3_of_bridge_witness
    {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBridge :
      HeytingLean.Topology.Knot.Kauffman.R3SkeinBridgeWitness g gL gR x u w) :
    HeytingLean.Topology.Knot.bracketSignature gL =
      HeytingLean.Topology.Knot.bracketSignature gR := by
  exact HeytingLean.Topology.Knot.virtual_class_respects_bracket_signature_r3_of_bridge_witness
    hLeft hRight hBridge

/--
R3 bracket hook via a bundled two-level bridge witness.
-/
theorem virtual_transport_bracket_hook_r3_of_two_level_bridge_witness
    {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwo :
      HeytingLean.Topology.Knot.Kauffman.R3TwoLevelBridgeWitness g x u w) :
    HeytingLean.Topology.Knot.bracketSignature gL =
      HeytingLean.Topology.Knot.bracketSignature gR := by
  exact
    HeytingLean.Topology.Knot.virtual_class_respects_bracket_signature_r3_of_two_level_bridge_witness
      hLeft hRight hTwo

end VirtualKnotTransportBridge
end PerspectivalPlenum
end HeytingLean
