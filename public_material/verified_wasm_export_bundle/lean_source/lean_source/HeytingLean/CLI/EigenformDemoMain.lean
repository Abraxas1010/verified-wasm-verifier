import HeytingLean.LambdaIR.Max01MiniCProof
import HeytingLean.LambdaIR.ToMiniC
import HeytingLean.MiniC.Semantics

/-!
# Eigenform demo CLI (Kauffman Phase 3)

This executable demonstrates a minimal fixed-point / eigenform equation `J = F(J)` using the
existing LambdaIR → MiniC pipeline:

* `F` is the LambdaIR nat→nat term `max01` (returns `1` on input `0`, otherwise returns the input).
* iterating from the bottom element `0` reaches the eigenform `J = 1` in one step.
* we cross-check the same behavior in the compiled MiniC fragment semantics.
-/

namespace HeytingLean.CLI.EigenformDemoMain

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Max01MiniCProof
open HeytingLean.LambdaIR.ToMiniC
open HeytingLean.MiniC

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private def okEq {α} [DecidableEq α] (x y : α) (msg : String) : IO Unit :=
  ok (decide (x = y)) msg

private def findFix (f : Nat → Nat) (x : Nat) : Nat → Option Nat
  | 0 => none
  | Nat.succ fuel =>
      let y := f x
      if y = x then
        some x
      else
        findFix f y fuel

private def findFixMiniC (fn : Fun) (x : Nat) : Nat → Option Nat
  | 0 => none
  | Nat.succ fuel =>
      match runNatFun fn x with
      | none => none
      | some y =>
          if y = x then
            some x
          else
            findFixMiniC fn y fuel

def main (_argv : List String) : IO UInt32 := do
  try
    let fIR : Nat → Nat := fun n =>
      LambdaIR.evalClosed (Term.app termMax01IR (Term.constNat n))

    okEq (fIR 0) (leanMax01 0) "LambdaIR semantics mismatch at input 0"
    okEq (fIR 0) 1 "Expected max01(0) = 1"

    let jIR := findFix fIR 0 8
    okEq jIR (some 1) "LambdaIR eigenform iteration did not stabilize at 1"
    match jIR with
    | none => throw (IO.userError "LambdaIR eigenform: missing result")
    | some j => okEq (fIR j) j "LambdaIR eigenform check failed: F(J) ≠ J"

    let fn ←
      match compileNatFun "max01" "x" termMax01IR with
      | .ok fn => pure fn
      | .error msg => throw (IO.userError s!"compileNatFun failed: {msg}")

    let jMini := findFixMiniC fn 0 8
    okEq jMini (some 1) "MiniC eigenform iteration did not stabilize at 1"
    match jMini with
    | none => throw (IO.userError "MiniC eigenform: missing result")
    | some j =>
        okEq (runNatFun fn j) (some j) "MiniC eigenform check failed: F(J) ≠ J"

    okEq jMini jIR "LambdaIR vs MiniC eigenform mismatch"

    IO.println "eigenform_demo: ok"
    pure 0
  catch e =>
    die s!"eigenform_demo: FAILED: {e}"

end HeytingLean.CLI.EigenformDemoMain

open HeytingLean.CLI.EigenformDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.EigenformDemoMain.main args

