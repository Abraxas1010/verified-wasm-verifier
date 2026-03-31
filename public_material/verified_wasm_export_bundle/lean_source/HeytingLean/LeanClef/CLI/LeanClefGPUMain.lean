import HeytingLean.LeanClef.Soundness
import HeytingLean.LeanClef.Export.HVM3

/-!
# LeanClef GPU-Parallel Proof Checking CLI

End-to-end pipeline: ICC term → verified type check → HVM3 emission → GPU execution.

The correctness sandwich:
1. **Verified input**: `checkProgram_iff` (sound + complete) certifies the term
2. **Untrusted oracle**: HVM3 reduces the term on CPU/GPU via interaction nets
3. **Optional verified output**: Lean kernel can re-check the normal form

DGX Spark unified memory: the GB10's NVLink-C2C means the interaction net heap
allocated by HVM3 (via mmap) is automatically GPU-accessible. Compiled mode (-c)
generates native C, compiled with gcc -O2 -flto for optimal throughput.

Usage:
  lake exe leanclef_gpu          # run end-to-end pipeline
-/

open LeanClef
open HeytingLean.LoF.ICC
open HeytingLean.LeanClef.Export.HVM3

/-- Counter for unique temp file names per pipeline run. -/
initialize tmpCounter : IO.Ref Nat ← IO.mkRef 0

/-- Run the full verified-check → HVM3-dispatch pipeline on a test term. -/
def runPipeline (name : String) (t : Term) (ann : DimAnnotation 8)
    (gradeAt : GradeAnnotation) : IO Unit := do
  IO.println s!"--- {name} ---"

  -- Step 1: Build program and run verified checker
  let P := buildProgram t ann gradeAt
  let checked := checkProgram P
  let dts := if decide (DTSConsistent P) then "PASS" else "FAIL"
  let phg := if decide (PHGGradeConsistent P) then "PASS" else "FAIL"
  IO.println s!"  Verified check: {if checked then "PASS" else "FAIL"} (DTS={dts}, PHG={phg})"

  if !checked then
    IO.println s!"  SKIP: term does not pass verified check"
    return

  -- Step 2: Emit HVM3 text
  let hvm3 := emitHVM3 t
  IO.println s!"  HVM3 text: {hvm3.trim}"

  -- Step 3: Write to unique temp file and invoke HVM3 in compiled mode (-c)
  -- Each term gets its own file to avoid stale .so caching issues
  let idx ← tmpCounter.modifyGet (fun n => (n, n + 1))
  let tmpPath := s!"/tmp/leanclef_dispatch_{idx}.hvm"
  IO.FS.writeFile tmpPath hvm3

  -- 30s timeout prevents runaway reductions
  let result ← IO.Process.output {
    cmd := "timeout"
    args := #["30", "/home/abraxas/.cabal/bin/hvm", "run", tmpPath, "-c", "-s"]
  }

  if result.exitCode == 0 then
    IO.println s!"  HVM3 result (compiled): {result.stdout.trim}"
  else if result.exitCode == 124 then
    IO.println s!"  HVM3 TIMEOUT (30s limit exceeded) — term may diverge"
  else
    IO.println s!"  HVM3 error (exit {result.exitCode}): {result.stderr.trim}"
  IO.println ""

def main : IO Unit := do
  IO.println "=== LeanClef GPU-Parallel Proof Checking Pipeline ==="
  IO.println "Each term is verified by checkProgram_iff, then dispatched to HVM3."
  IO.println "DGX Spark GB10 | Unified Memory | Compiled Mode (-c)"
  IO.println ""

  let zeroAnn : DimAnnotation 8 := ⟨fun _ => DTS.zeroDimension⟩
  let noGrade : GradeAnnotation := fun _ => none

  -- Pipeline 1: Identity (λx.x)
  runPipeline "identity (λx.x)" (.lam (.var 0)) zeroAnn noGrade

  -- Pipeline 2: Beta redex (λy. (λx.x) y) — closed beta redex
  runPipeline "beta (λy.(λx.x) y)"
    (.lam (.app (.lam (.var 0)) (.var 0))) zeroAnn noGrade

  -- Pipeline 3: K combinator (λx.λ_.x)
  runPipeline "K combinator" (.lam (.lam (.var 1))) zeroAnn noGrade

  -- Pipeline 4: Bridge term
  runPipeline "bridge (var 0)" (.bridge (.var 0)) zeroAnn noGrade

  -- Pipeline 5: Annotation (erased at runtime)
  runPipeline "ann (lam var0) (var 0)" (.ann (.lam (.var 0)) (.var 0)) zeroAnn noGrade

  -- Pipeline 6: Self-application (dup test — λx. x x)
  runPipeline "self-app (λx. x x)"
    (.lam (.app (.var 0) (.var 0))) zeroAnn noGrade

  -- Pipeline 7: Church 2 applied (λf.λx. f(f x)) — f duplicated
  runPipeline "Church 2 (λf.λx. f(f x))"
    (.lam (.lam (.app (.var 1) (.app (.var 1) (.var 0))))) zeroAnn noGrade

  IO.println "=== Pipeline complete ==="
  IO.println "All verdicts backed by checkProgram_iff (0 gaps, 0 axioms)"
