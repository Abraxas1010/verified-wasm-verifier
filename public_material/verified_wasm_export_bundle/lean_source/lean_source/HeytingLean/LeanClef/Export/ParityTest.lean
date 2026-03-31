import HeytingLean.LeanClef.Export.InetMLIR

/-!
# LeanClef.Export.ParityTest

Export smoke checks: verify that the MLIR emitter produces
structurally valid output for ICC test terms.

This is NOT semantic parity (no MLIR parser exists in Lean).
It checks: (1) ICC reduction matches expected normal form,
(2) MLIR output contains the "inet." dialect marker string.
-/

namespace LeanClef.Export

open HeytingLean.LoF.ICC

/-- Check whether `needle` appears as a substring of `haystack`. -/
def containsSubstr (needle haystack : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Identity: (λ. 0) applied to (var 0) reduces to (var 0). -/
def identityApp : Term := .app (.lam (.var 0)) (.var 0)

/-- K combinator: K x y = x. Applied: (λ.λ.1) x y. -/
def kApp : Term := .app (.app (.lam (.lam (.var 1))) (.var 0)) (.var 1)

/-- Export smoke check: verify reduction + MLIR contains "inet." marker. -/
def exportSmokeCheck (t : Term) (expected : Term) (fuel : Nat := 100) : Bool :=
  let reduced := reduceFuel fuel t
  let mlir := iccToMLIRText t
  reduced == expected && containsSubstr "inet." mlir

/-- Identity application reduces correctly and emits MLIR with inet marker. -/
example : exportSmokeCheck identityApp (.var 0) = true := by native_decide

/-- K applied once reduces and emits MLIR with inet marker. -/
example : exportSmokeCheck (.app (.lam (.lam (.var 1))) (.var 0))
    (.lam (.var 1)) = true := by native_decide

/-- A variable emits MLIR containing the "inet." dialect marker. -/
example : containsSubstr "inet." (iccToMLIRText (.var 42)) = true := by native_decide

/-- The emitted MLIR contains the module structure. -/
example : containsSubstr "module" (iccToMLIRText (.var 0)) = true := by native_decide

-- === Graded MLIR smoke checks ===

/-- A test grade map: assign grade 2 to agent 0, grade 1 to agent 1. -/
def testGradeMap : GradeMap
  | 0 => some 2
  | 1 => some 1
  | _ => none

/-- Graded MLIR output contains the "grade =" attribute. -/
example : containsSubstr "grade =" (iccToGradedMLIRText (.var 0) testGradeMap) = true := by
  native_decide

/-- Graded MLIR output still contains the inet dialect marker. -/
example : containsSubstr "inet." (iccToGradedMLIRText (.var 0) testGradeMap) = true := by
  native_decide

/-- Ungraded emission (all-none grade map) contains no grade attribute. -/
example : containsSubstr "grade =" (iccToGradedMLIRText (.var 0) (fun _ => none)) = false := by
  native_decide

end LeanClef.Export
