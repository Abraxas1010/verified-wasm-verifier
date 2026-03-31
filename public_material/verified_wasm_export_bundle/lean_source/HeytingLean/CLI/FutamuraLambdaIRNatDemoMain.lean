import HeytingLean.ProgramCalculus.Futamura
import HeytingLean.ProgramCalculus.Instances.LambdaIRNatNat
import HeytingLean.LambdaIR.ToMiniC

/-!
# `futamura_lambda_ir_nat_demo`

Repo-local Futamura-1 demo for a tiny closed LambdaIR fragment with a nontrivial code type:

* Codes are `Nat` (static input).
* Dynamic input is a `Nat`.
* The interpreter is a LambdaIR term of type `Nat → Nat → Nat` (adds the code to the input).
* Specialization produces a residual `Nat → Nat` term, which is then compiled to MiniC and run.
-/

namespace HeytingLean.CLI.FutamuraLambdaIRNatDemoMain

open HeytingLean
open HeytingLean.ProgramCalculus
open HeytingLean.ProgramCalculus.Instances
open HeytingLean.Core
open HeytingLean.LambdaIR

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private def okEq {α} [DecidableEq α] (x y : α) (msg : String) : IO Unit :=
  ok (decide (x = y)) msg

private def checkOne (k : Nat) (n : Nat) : IO Unit := do
  let residual : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat) :=
    ProgramCalculus.compile lambdaIRNatNatMix lambdaIRNatNatInterpModel k
  IO.println s!"[lambda-ir-nat] code={k} residual.size={LambdaIR.Term.size residual}"
  IO.println s!"[lambda-ir-nat] residual={reprStr residual}"

  let outResidual : Nat :=
    LambdaIR.evalClosed (LambdaIR.Term.app residual (LambdaIR.Term.constNat n))
  let outSpec : Nat := lambdaIRNatNatCodeSem k n
  okEq outResidual outSpec s!"[lambda-ir-nat] mismatch: residual={outResidual} codeSem={outSpec}"

  -- Exercise the (in-repo) LambdaIR → MiniC compiler on the residual function.
  let funName := s!"futamura_lambda_ir_nat_residual_{k}"
  let param := "n"
  match LambdaIR.ToMiniC.compileNatFun funName param residual with
  | .error err => throw <| IO.userError s!"[lambda-ir-nat] MiniC compile failed: {err}"
  | .ok fn =>
      match HeytingLean.MiniC.runNatFunFrag fn param n with
      | none => throw <| IO.userError "[lambda-ir-nat] MiniC exec failed"
      | some outMiniC =>
          okEq outMiniC outSpec s!"[lambda-ir-nat] MiniC mismatch: got={outMiniC} expected={outSpec}"

def main (_argv : List String) : IO UInt32 := do
  try
    let n := 7
    checkOne 3 n
    checkOne 10 n
    IO.println "futamura_lambda_ir_nat_demo: ok"
    pure 0
  catch e =>
    die s!"futamura_lambda_ir_nat_demo: FAILED: {e}"

end HeytingLean.CLI.FutamuraLambdaIRNatDemoMain

open HeytingLean.CLI.FutamuraLambdaIRNatDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FutamuraLambdaIRNatDemoMain.main args

