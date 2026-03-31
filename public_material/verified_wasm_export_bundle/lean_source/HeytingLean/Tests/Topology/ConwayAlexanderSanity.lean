import HeytingLean.Topology.Knot.AlexanderMathlib
import HeytingLean.Topology.Knot.Braid

/-!
# Sanity checks: Conway/Alexander layer

These tests verify that the new executable layers:
- evaluate successfully on canonical fixtures,
- satisfy the local skein identity at the evaluator boundary.
-/

namespace HeytingLean.Tests.Topology.ConwayAlexanderSanity

open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Kauffman

private def isOk {α} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

private def okEq (e : Except String LaurentPoly) (x : LaurentPoly) : Bool :=
  match e with
  | .ok y => decide (y = x)
  | .error _ => false

private def unlink₂ : Kauffman.SignedPDGraph :=
  { graph := { freeLoops := 2, n := 0, arcNbr := #[] }, sign := #[] }

private def hopfPos : Except String Kauffman.SignedPDGraph :=
  Braid.closureSignedPDGraph 2
    [{ i := 0, sign := .pos }, { i := 0, sign := .pos }]

private def trefoilPos : Except String Kauffman.SignedPDGraph :=
  Braid.closureSignedPDGraph 2
    [{ i := 0, sign := .pos }, { i := 0, sign := .pos }, { i := 0, sign := .pos }]

example : okEq (Kauffman.SignedPDGraph.conway unlink₂) 0 = true := by
  native_decide

example : okEq (Kauffman.SignedPDGraph.alexander unlink₂) 0 = true := by
  native_decide

example : isOk (hopfPos.bind Kauffman.SignedPDGraph.conway) = true := by
  native_decide

example : isOk (hopfPos.bind Kauffman.SignedPDGraph.alexander) = true := by
  native_decide

example : okEq (hopfPos.bind Kauffman.SignedPDGraph.conway) 0 = true := by
  native_decide

example : okEq (hopfPos.bind Kauffman.SignedPDGraph.alexander) 0 = true := by
  native_decide

example : isOk (trefoilPos.bind Kauffman.SignedPDGraph.conway) = true := by
  native_decide

example : isOk (trefoilPos.bind Kauffman.SignedPDGraph.alexander) = true := by
  native_decide

example : okEq (trefoilPos.bind Kauffman.SignedPDGraph.conway) 0 = true := by
  native_decide

example : okEq (trefoilPos.bind Kauffman.SignedPDGraph.alexander) 0 = true := by
  native_decide

private def localSkeinWitness : Bool :=
  match Braid.closureSignedPDGraph 2 [{ i := 0, sign := .pos }] with
  | .error _ => false
  | .ok sp =>
      match Kauffman.SignedPDGraph.validate sp with
      | .error _ => false
      | .ok _ =>
          match Kauffman.SignedPDGraph.lMinusLast sp, Kauffman.SignedPDGraph.lZeroLast sp with
          | .ok sm, .ok s0 =>
              match Kauffman.SignedPDGraph.conwayWithFuel 3 sp,
                    Kauffman.SignedPDGraph.conwayWithFuel 2 sm,
                    Kauffman.SignedPDGraph.conwayWithFuel 2 s0 with
              | .ok pp, .ok pm, .ok p0 =>
                  pp == pm + Kauffman.z * p0
              | _, _, _ => false
          | _, _ => false

example : localSkeinWitness = true := by
  native_decide

end HeytingLean.Tests.Topology.ConwayAlexanderSanity
