import HeytingLean.Core.Types
import HeytingLean.LambdaIR.Syntax
import HeytingLean.LambdaIR.Semantics
import HeytingLean.LambdaIR.ToMiniC

open HeytingLean
open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.ToMiniC

namespace HeytingLean.Tests.PipelineMin2Smoke

/-- A tiny LambdaIR term λ n, min(n,2). -/
def lamMin2 : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat) :=
  let body := LambdaIR.Term.if_
    (LambdaIR.Term.app (LambdaIR.Term.app LambdaIR.Term.primEqNat (LambdaIR.Term.var Var.vz)) (LambdaIR.Term.constNat 0))
    (LambdaIR.Term.constNat 0)
    (LambdaIR.Term.if_
      (LambdaIR.Term.app (LambdaIR.Term.app LambdaIR.Term.primEqNat (LambdaIR.Term.var Var.vz)) (LambdaIR.Term.constNat 1))
      (LambdaIR.Term.constNat 1)
      (LambdaIR.Term.constNat 2))
  LambdaIR.Term.lam body

/-- Evaluate the compiled function at n via MiniC fragment semantics. -/
def evalCompiled (n : Nat) : Option Nat :=
  runCompiledNatFunFrag "min2" "n" lamMin2 n

/-- Evaluate the LambdaIR closed application at n. -/
def evalIR (n : Nat) : Nat :=
  LambdaIR.evalClosed (LambdaIR.Term.app lamMin2 (LambdaIR.Term.constNat n))

/-- IO test: checks several inputs agree. -/
def run : IO Unit := do
  for n in [0,1,2,3,4,41,100] do
    match evalCompiled n with
    | some m =>
      if m = evalIR n then pure () else throw <| IO.userError s!"Mismatch min2 at {n}: compiled={m} ir={evalIR n}"
    | none => throw <| IO.userError s!"Compilation produced none at {n}"

end HeytingLean.Tests.PipelineMin2Smoke

/-- Lake entry point. -/
def main (_args : List String) : IO UInt32 := do
  try
    HeytingLean.Tests.PipelineMin2Smoke.run
    IO.println "Pipeline min2 smoke passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1
