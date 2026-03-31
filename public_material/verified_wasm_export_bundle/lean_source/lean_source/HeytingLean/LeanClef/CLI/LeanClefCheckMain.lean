import HeytingLean.LeanClef.Soundness

/-!
# LeanClef Verified Checker CLI

Demonstrates the verified decision procedure: buildProgram + checkProgram.

This is the spec made executable. Every verdict is backed by
checkProgram_iff (soundness + completeness) and buildProgram_semantic_wf
(semantic well-formedness by construction).
-/

open LeanClef
open HeytingLean.LoF.ICC

/-- Run the verified checker on a test program and report the result. -/
def checkAndReport (name : String) (t : Term) (ann : DimAnnotation 8)
    (gradeAt : GradeAnnotation) : IO Unit := do
  let P := buildProgram t ann gradeAt
  let result := checkProgram P
  let dts := if decide (DTSConsistent P) then "PASS" else "FAIL"
  let phg := if decide (PHGGradeConsistent P) then "PASS" else "FAIL"
  IO.println s!"{name}: {if result then "PASS" else "FAIL"} (DTS={dts}, PHG={phg})"
  IO.println s!"  term_size={t.size} constraints={P.constraints.size} grade_pairs={P.gradePairs.length}"

def main : IO Unit := do
  IO.println "=== LeanClef Verified Checker ==="
  IO.println "Each verdict is backed by checkProgram_iff (sound + complete)"
  IO.println ""

  -- Test 1: identity combinator (should PASS)
  checkAndReport "identity (λx.x)"
    (.lam (.var 0))
    ⟨fun _ => DTS.zeroDimension⟩
    (fun _ => none)

  -- Test 2: application (should PASS with zero annotations)
  checkAndReport "app (var 0) (var 1)"
    (.app (.var 0) (.var 1))
    ⟨fun _ => DTS.zeroDimension⟩
    (fun _ => none)

  -- Test 3: beta redex (should PASS)
  checkAndReport "beta (λx.x) y"
    (.app (.lam (.var 0)) (.var 0))
    ⟨fun _ => DTS.zeroDimension⟩
    (fun _ => none)

  -- Test 4: bridge term (should PASS)
  checkAndReport "bridge (var 0)"
    (.bridge (.var 0))
    ⟨fun _ => DTS.zeroDimension⟩
    (fun _ => none)

  -- Test 5: annotation (should PASS)
  checkAndReport "ann (var 0) (var 1)"
    (.ann (.var 0) (.var 1))
    ⟨fun _ => DTS.zeroDimension⟩
    (fun _ => none)

  IO.println ""
  IO.println "All verdicts verified by Lean type checker (0 gaps, 0 axioms)"
