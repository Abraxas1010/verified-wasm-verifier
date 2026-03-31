import HeytingLean.LeanCoreV2.Syntax
import HeytingLean.LeanCoreV2.Semantics

open HeytingLean.Core
open HeytingLean.LeanCoreV2

namespace HeytingLean.Tests.LeanCoreV2

/-- Identity function on natural numbers. -/
def idNat : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam (Γ:=[]) (α:=Ty.nat) (β:=Ty.nat) (Term.var Var.vz)

/-- Add-one function using the built-in primitive addition. -/
def add1 : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam <|
    Term.app
      (Term.app Term.primAddNat (Term.var Var.vz))
      (Term.constNat 1)

/-- Boolean negation via `if`. -/
def notBool : Term [] (Ty.arrow Ty.bool Ty.bool) :=
  Term.lam <|
    Term.if_ (Term.var Var.vz)
      (Term.constBool false)
      (Term.constBool true)

/-- Helper to assert equality and produce IO failure on mismatch. -/
def expectEq (msg : String) {α} [DecidableEq α] (a b : α) : IO Unit := do
  if decide (a = b) then pure ()
  else throw <| IO.userError s!"LeanCoreV2 test failed: {msg}"

/-- Runs a few basic LeanCore v2 evaluations. -/
def run : IO Unit := do
  expectEq (α := Nat) "idNat 5" (evalClosed (Term.app idNat (Term.constNat 5))) (5 : Nat)
  expectEq (α := Nat) "add1 41" (evalClosed (Term.app add1 (Term.constNat 41))) (42 : Nat)
  expectEq (α := Bool) "notBool true" (evalClosed (Term.app notBool (Term.constBool true))) (false : Bool)
  expectEq (α := Bool) "notBool false" (evalClosed (Term.app notBool (Term.constBool false))) (true : Bool)

/-- CLI entry point for the lake test target. -/
def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "LeanCoreV2 basics passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.LeanCoreV2

/-- Entry point for the `lake exe test_leancore_v2_basics` target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.LeanCoreV2.main args
