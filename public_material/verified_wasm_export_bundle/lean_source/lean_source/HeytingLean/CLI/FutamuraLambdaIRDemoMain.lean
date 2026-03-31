import HeytingLean.ProgramCalculus.Futamura
import HeytingLean.ProgramCalculus.Instances.LambdaIRBoolNat
import HeytingLean.LambdaIR.ToMiniC

/-!
# `futamura_lambda_ir_demo`

End-to-end, repo-local Futamura-1 demo for a tiny closed LambdaIR fragment:

* Codes are `Bool` (static input).
* Dynamic input is a `Nat`.
* The interpreter is a LambdaIR term of type `Bool → Nat → Nat`.
* Specialization produces a residual `Nat → Nat` term, which is then compiled to MiniC and run.
-/

namespace HeytingLean.CLI.FutamuraLambdaIRDemoMain

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

private def checkOne (b : Bool) (n : Nat) : IO Unit := do
  let residual : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat) :=
    ProgramCalculus.compile lambdaIRBoolNatMix lambdaIRBoolNatInterpModel b
  IO.println s!"[lambda-ir] code={b} residual.size={LambdaIR.Term.size residual}"
  IO.println s!"[lambda-ir] residual={reprStr residual}"

  let outResidual : Nat :=
    LambdaIR.evalClosed (LambdaIR.Term.app residual (LambdaIR.Term.constNat n))
  let outSpec : Nat := lambdaIRBoolNatCodeSem b n
  okEq outResidual outSpec s!"[lambda-ir] mismatch: residual={outResidual} codeSem={outSpec}"

  -- Exercise the (in-repo) LambdaIR → MiniC compiler on the residual function.
  let funName := s!"futamura_lambda_ir_residual_{b}"
  let param := "n"
  match LambdaIR.ToMiniC.compileNatFun funName param residual with
  | .error err => throw <| IO.userError s!"[lambda-ir] MiniC compile failed: {err}"
  | .ok fn =>
      match HeytingLean.MiniC.runNatFunFrag fn param n with
      | none => throw <| IO.userError "[lambda-ir] MiniC exec failed"
      | some outMiniC =>
          okEq outMiniC outSpec s!"[lambda-ir] MiniC mismatch: got={outMiniC} expected={outSpec}"

def main (_argv : List String) : IO UInt32 := do
  try
    let n := 7
    checkOne true n
    checkOne false n
    IO.println "futamura_lambda_ir_demo: ok"
    pure 0
  catch e =>
    die s!"futamura_lambda_ir_demo: FAILED: {e}"

end HeytingLean.CLI.FutamuraLambdaIRDemoMain

open HeytingLean.CLI.FutamuraLambdaIRDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FutamuraLambdaIRDemoMain.main args
