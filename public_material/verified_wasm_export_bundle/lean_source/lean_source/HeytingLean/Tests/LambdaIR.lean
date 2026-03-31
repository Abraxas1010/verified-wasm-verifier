import HeytingLean.LambdaIR.Syntax
import HeytingLean.LambdaIR.Semantics

open HeytingLean.Core
open HeytingLean.LambdaIR

namespace HeytingLean.Tests.LambdaIR

def idNat : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam (Term.var Var.vz)

def add1 : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam (Term.app (Term.app Term.primAddNat (Term.var Var.vz)) (Term.constNat 1))

def expectEq (msg : String) {α} [DecidableEq α] (a b : α) : IO Unit := do
  if decide (a = b) then
    pure ()
  else
    throw <| IO.userError s!"LambdaIR test failed: {msg}"

def run : IO Unit := do
  expectEq (α := Nat) "idNat 7" (evalClosed (Term.app idNat (Term.constNat 7))) (7 : Nat)
  expectEq (α := Nat) "add1 41" (evalClosed (Term.app add1 (Term.constNat 41))) (42 : Nat)

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "LambdaIR basics passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.LambdaIR

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.LambdaIR.main args
