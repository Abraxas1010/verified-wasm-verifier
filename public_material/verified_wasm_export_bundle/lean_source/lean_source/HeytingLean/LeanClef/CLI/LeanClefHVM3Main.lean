import HeytingLean.LeanClef.Export.HVM3

/-!
# LeanClef HVM3 Emitter CLI

Emit ICC test terms as HVM3 source text. This is the standalone
emitter that demonstrates ICC.Term → HVM3 text translation with
linearity analysis (erasure / linear / duplication).

Usage:
  lake exe leanclef_hvm3              # emit all test terms
  lake exe leanclef_hvm3 | hvm run /dev/stdin -s   # run via HVM3
-/

open HeytingLean.LoF.ICC
open HeytingLean.LeanClef.Export.HVM3

/-- Emit a single test term and print both the HVM3 text and term info. -/
def emitAndReport (name : String) (t : Term) : IO Unit := do
  let hvm3 := emitHVM3 t
  IO.println s!"--- {name} (size={t.size}) ---"
  IO.println hvm3

def main : IO Unit := do
  IO.println "=== LeanClef HVM3 Emitter ==="
  IO.println ""

  -- Test 1: Identity (λx. x) — linear variable
  emitAndReport "identity" (.lam (.var 0))

  -- Test 2: K combinator (λx. λ_. x) — one erased, one linear
  emitAndReport "K combinator" (.lam (.lam (.var 1)))

  -- Test 3: Closed beta redex λy. (λx. x) y
  emitAndReport "closed beta" (.lam (.app (.lam (.var 0)) (.var 0)))

  -- Test 4: Self-application (λx. x x) — duplication needed
  emitAndReport "self-app (dup)" (.lam (.app (.var 0) (.var 0)))

  -- Test 5: Bridge term — compiles to lambda
  emitAndReport "bridge" (.bridge (.var 0))

  -- Test 6: Annotation — type erased at runtime
  emitAndReport "annotation" (.ann (.lam (.var 0)) (.var 0))

  -- Test 7: Closed beta chain λz. (λx. x) ((λy. y) z)
  emitAndReport "closed beta chain"
    (.lam (.app (.lam (.var 0)) (.app (.lam (.var 0)) (.var 0))))

  -- Test 8: Nested lambda (λx. λy. x y) — both linear
  emitAndReport "nested lam" (.lam (.lam (.app (.var 1) (.var 0))))

  IO.println "=== Done ==="
