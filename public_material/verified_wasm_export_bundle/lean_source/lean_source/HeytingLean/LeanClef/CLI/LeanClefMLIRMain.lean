import HeytingLean.LeanClef.Export.InetMLIR

/-!
# LeanClef MLIR CLI

Emit ICC terms as Inet MLIR text to stdout.
Demonstrates the verified lowering pipeline: ICC → ICCNet → MLIR.
-/

open LeanClef.Export
open HeytingLean.LoF.ICC

def main : IO Unit := do
  -- Demo: identity combinator applied to var 0
  -- (λ. 0) applied to (var 0) — a β-redex
  let term := Term.app (.lam (.var 0)) (.var 0)
  IO.println (iccToMLIRText term)
