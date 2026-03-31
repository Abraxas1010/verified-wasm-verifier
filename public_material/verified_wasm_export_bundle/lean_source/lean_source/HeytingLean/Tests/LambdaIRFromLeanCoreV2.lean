import HeytingLean.LeanCoreV2.Bridge
import HeytingLean.LeanCoreV2.ToLambdaIR
import HeytingLean.LambdaIR.Semantics

open HeytingLean
open HeytingLean.Core
open LeanCoreV2
open LeanCoreV2.Bridge
open LeanCoreV2.ToLambdaIR
open LambdaIR

namespace HeytingLean.Tests.LambdaIRFromLeanCoreV2

/-- LambdaIR version of the add1 term via translation. -/
def termAdd1IR : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat) :=
  translateTerm Bridge.termAdd1

/-- Semantics preservation corollary: LeanCoreV2 add1 equals LambdaIR add1. -/
theorem add1_ir_bridge_correct (n : Nat) :
    LambdaIR.evalClosed (LambdaIR.Term.app termAdd1IR (LambdaIR.Term.constNat n))
      = Bridge.leanAdd1 n := by
  have htrans :=
    translate_eval_closed
      (LeanCoreV2.Term.app Bridge.termAdd1 (LeanCoreV2.Term.constNat n))
  have hcore := Bridge.add1_bridge_correct n
  simpa [termAdd1IR, translateTerm, Bridge.leanAdd1] using htrans.trans hcore

def expectEq (msg : String) {α} [DecidableEq α] (a b : α) : IO Unit := do
  if decide (a = b) then
    pure ()
  else
    throw <| IO.userError s!"LambdaIR bridge test failed: {msg}"

def run : IO Unit := do
  for n in [0, 1, 41, 100] do
    let irVal :=
      LambdaIR.evalClosed (LambdaIR.Term.app termAdd1IR (LambdaIR.Term.constNat n))
    let lcVal := Bridge.leanAdd1 n
    expectEq (α := Nat) s!"add1 bridge at {n}" irVal lcVal

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "LambdaIRFromLeanCoreV2 bridge passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.LambdaIRFromLeanCoreV2

/-- Expose the lake executable entry point. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.LambdaIRFromLeanCoreV2.main args
