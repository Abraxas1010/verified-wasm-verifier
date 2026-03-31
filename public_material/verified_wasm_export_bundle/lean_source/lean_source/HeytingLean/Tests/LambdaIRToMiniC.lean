import HeytingLean.LambdaIR.NatExamplesRegistry
import HeytingLean.LambdaIR.Nat2ExamplesRegistry
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.Nat2CompileFrag
import HeytingLean.LambdaIR.ToMiniC
import HeytingLean.MiniC.Semantics

open HeytingLean
open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatExamplesRegistry
open HeytingLean.LambdaIR.Nat2ExamplesRegistry
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.LambdaIR.Nat2CompileFrag
open HeytingLean.LambdaIR.ToMiniC
open HeytingLean.MiniC

namespace HeytingLean.Tests

/-- CLI-style smoke test for LambdaIR → MiniC. -/
def main (_args : List String) : IO UInt32 := do
  -- Anchor the proofs so regressions are caught at compile time.
  for ex in NatExamplesRegistry.examples do
    let _ := ex.endToEndProof
    if ex.lofProps.isEmpty then
      throw <|
        IO.userError s!"LoF manifest missing for nat example {ex.funName}"
    for p in ex.lofProps do
      let _ := p.proof
  for ex in Nat2ExamplesRegistry.examples do
    let _ := ex.endToEndProof
    if ex.lofProps.isEmpty then
      throw <|
        IO.userError s!"LoF manifest missing for nat2 example {ex.funName}"
    for p in ex.lofProps do
      let _ := p.proof
  let inputs : List Nat := [0, 1, 2, 5, 10, 41]
  for ex in NatExamplesRegistry.examples do
    match compileNatFun ex.funName ex.paramName ex.term with
    | Except.error msg =>
        IO.eprintln
          s!"LambdaIR→MiniC compile error for {ex.funName}: {msg}"
        return 1
    | Except.ok fn => do
        for n in inputs do
          let miniVal := runNatFun fn n
          let expected := ex.leanF n
          if miniVal = some expected then
            IO.println s!"{ex.funName}({n}) ok"
          else
            throw <|
              IO.userError
                s!"LambdaIR→MiniC mismatch for {ex.funName} at input {n}: expected {expected}, got {miniVal}"
  for ex in Nat2ExamplesRegistry.examples do
    let fn := compileNat2FunFrag ex.funName ex.param1 ex.param2 ex.term
    for x in inputs do
      for y in inputs do
        let miniVal :=
          runNat2FunFrag fn ex.param1 ex.param2 x y
        let expected := ex.leanF x y
        if miniVal = some expected then
          IO.println s!"{ex.funName}({x}, {y}) ok"
        else
          throw <|
            IO.userError
              s!"LambdaIR→MiniC mismatch for {ex.funName} at inputs ({x}, {y}): expected {expected}, got {miniVal}"
  IO.println "LambdaIR→MiniC smoke test passed"
  pure 0

end HeytingLean.Tests

/-- expose entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.main args
