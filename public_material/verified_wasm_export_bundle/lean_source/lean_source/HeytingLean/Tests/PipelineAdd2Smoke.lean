import HeytingLean.Core.Types
import HeytingLean.LambdaIR.Syntax
import HeytingLean.LambdaIR.Semantics
import HeytingLean.LambdaIR.ToMiniC

open HeytingLean
open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.ToMiniC

namespace HeytingLean.Tests.PipelineAdd2Smoke

/-- A tiny LambdaIR term λ n, (n + n). -/
def lamAdd2 : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat) :=
  LambdaIR.Term.lam (LambdaIR.Term.app (LambdaIR.Term.app LambdaIR.Term.primAddNat (LambdaIR.Term.var Var.vz)) (LambdaIR.Term.var Var.vz))

/-- Evaluate the compiled function at n via MiniC fragment semantics. -/
def evalCompiled (n : Nat) : Option Nat :=
  runCompiledNatFunFrag "add2" "n" lamAdd2 n

/-- Evaluate the LambdaIR closed application at n. -/
def evalIR (n : Nat) : Nat :=
  LambdaIR.evalClosed (LambdaIR.Term.app lamAdd2 (LambdaIR.Term.constNat n))

/-- IO test: checks several inputs agree. -/
def run : IO Unit := do
  for n in [0,1,2,7,41,100] do
    match evalCompiled n with
    | some m =>
      if m = evalIR n then pure () else throw <| IO.userError s!"Mismatch add2 at {n}: compiled={m} ir={evalIR n}"
    | none => throw <| IO.userError s!"Compilation produced none at {n}"

end HeytingLean.Tests.PipelineAdd2Smoke

/-- Lake entry point. -/
def main (_args : List String) : IO UInt32 := do
  try
    HeytingLean.Tests.PipelineAdd2Smoke.run
    IO.println "Pipeline add2 smoke passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1
