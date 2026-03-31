import HeytingLean.Topology.Knot.VirtualTransport
import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR1
import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR2
import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR3
import HeytingLean.Topology.Knot.ConwayMathlib

/-!
# Knot.VirtualInvariantBridge

Phase-K3 compatibility layer between virtual transport classes and existing
knot invariant APIs.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open Reidemeister

noncomputable section

/-- Proof-facing alias for the Mathlib Kauffman bracket signature. -/
def bracketSignature (g : PDGraph) : Except String Kauffman.PolyML :=
  Kauffman.bracketGraphML g

/-- Proof-facing alias for the executable Conway signature. -/
def conwaySignature (s : Kauffman.SignedPDGraph) : Except String Kauffman.ConwayPoly :=
  Kauffman.SignedPDGraph.conway s

/-- Signed variant of the virtual class predicate. -/
def SignedVirtualClass (s : Kauffman.SignedPDGraph) : Prop :=
  Kauffman.SignedPDGraph.validate s = .ok ()

/--
Primary K3 theorem: R2 transport preserves the bracket signature exactly.
-/
theorem virtual_class_respects_bracket_signature
    {g g' : PDGraph} {x u : Nat}
    (hMove : Reidemeister.r2Add g x u = .ok g') :
    bracketSignature g' = bracketSignature g := by
  simpa [bracketSignature] using Kauffman.bracketGraphML_r2Add (g := g) (g' := g') (x := x) (u := u) hMove

/--
R1-positive compatibility: bracket signature transforms by the standard
`-(A^3)` scaling factor.
-/
theorem virtual_class_respects_bracket_signature_r1_pos
    {g g' : PDGraph} {x : Nat}
    (hMove : Reidemeister.r1Add g x .pos = .ok g') :
    bracketSignature g' =
      (do
        let b ← bracketSignature g
        return (-(Kauffman.AML ^ 3 : Kauffman.PolyML)) * b) := by
  simpa [bracketSignature] using Kauffman.bracketGraphML_r1Add_pos (g := g) (g' := g') (x := x) hMove

/--
R3 compatibility endpoint (conditional, no axioms):
if the two braid endpoints have equal one-step skein evaluators, their bracket
signatures coincide.
-/
theorem virtual_class_respects_bracket_signature_r3_of_skeinStep_eq
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hStepEq : Kauffman.r3SkeinStep gL = Kauffman.r3SkeinStep gR) :
    bracketSignature gL = bracketSignature gR := by
  simpa [bracketSignature] using
    Kauffman.bracketGraphML_r3_invariant_of_skeinStep_eq
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hStepEq

/--
R3 compatibility endpoint via TL3 bridge correspondences (endpoint form).
-/
theorem virtual_class_respects_bracket_signature_r3_of_tl3_bridge_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftTL :
      Kauffman.r3SkeinStep gL =
        Kauffman.TL3Context.evalTL3Expr fuel g x u w Kauffman.R3.tlWordLeft)
    (hRightTL :
      Kauffman.r3SkeinStep gR =
        Kauffman.TL3Context.evalTL3Expr fuel g x u w Kauffman.R3.tlWordRight) :
    bracketSignature gL = bracketSignature gR := by
  simpa [bracketSignature] using
    Kauffman.bracketGraphML_r3_invariant_of_tl3_bridge_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftTL hRightTL

/--
R3 compatibility endpoint via the unified bridge witness.

This allows callers to provide either a direct skein-step equality witness or
endpoint TL3 bridge correspondences through
`Kauffman.R3SkeinBridgeWitness`.
-/
theorem virtual_class_respects_bracket_signature_r3_of_bridge_witness
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBridge : Kauffman.R3SkeinBridgeWitness g gL gR x u w) :
    bracketSignature gL = bracketSignature gR := by
  simpa [bracketSignature] using
    Kauffman.bracketGraphML_r3_invariant_of_bridge_witness
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hBridge

/--
R3 compatibility endpoint via a bundled two-level bridge witness.

This is the scoped constructive path that replaces the over-strong unconditional
endpoint claim.
-/
theorem virtual_class_respects_bracket_signature_r3_of_two_level_bridge_witness
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwo : Kauffman.R3TwoLevelBridgeWitness g x u w) :
    bracketSignature gL = bracketSignature gR := by
  simpa [bracketSignature] using
    Kauffman.bracketGraphML_r3_invariant_of_two_level_bridge_witness_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hTwo

/--
K3 Conway compatibility theorem: under a valid signed state with positive last
crossing, the Conway evaluator obeys the expected local decomposition step.
-/
theorem virtual_class_respects_conway_signature
    {fuel : Nat} {s : Kauffman.SignedPDGraph}
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
  exact Kauffman.SignedPDGraph.conwayWithFuel_pos_step_eq
    (fuel := fuel) (sp := s) hClass hn hSign

end

end Knot
end Topology
end HeytingLean
