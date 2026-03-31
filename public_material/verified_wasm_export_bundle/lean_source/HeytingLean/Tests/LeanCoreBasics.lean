import HeytingLean.LeanCore.Syntax
import HeytingLean.LeanCore.Typing
import HeytingLean.LeanCore.Semantics

open HeytingLean.LeanCore

namespace HeytingLean.Tests

private def natTy : Ty := Ty.base .nat

private def prim : PrimEnv :=
  [{ name := "zero", ty := natTy }]

private def idNat : Term (Ty.arrow natTy natTy) :=
  Term.lam (Term.var 0)

private def sample : Term natTy :=
  Term.app idNat (Term.const (τ:=natTy) "zero")

/-- Typing proof for the identity function. -/
theorem idNat_typed : HasType prim [] idNat := by
  apply HasType.lam
  simpa using (HasType.var (prim:=prim) (Γ:=[natTy]) (idx:=0) (τ:=natTy) rfl)

/-- Typing proof for the sample expression. -/
theorem sample_typed : HasType prim [] sample := by
  apply HasType.app idNat_typed
  exact HasType.const (prim:=prim) (Γ:=[]) (τ:=natTy) (name:="zero") rfl

/-- Simple regression: evaluate the closed term and ensure it reduces to `zero`. -/
def run (_args : List String) : IO UInt32 := do
  match evalClosed (PrimSemEnv.default) sample with
  | some (Value.vnat 0) =>
      IO.println "LeanCore basics sanity check passed"
      pure 0
  | some _ =>
      IO.eprintln "Unexpected value"
      pure 1
  | none =>
      IO.eprintln "Evaluator returned none"
      pure 1

end HeytingLean.Tests

def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.run args
