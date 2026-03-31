import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.FullKernelSKY

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

def sortZero : FullKernelSKY.E :=
  .sort .zero

def sortOne : FullKernelSKY.E :=
  .sort (.succ .zero)

def sortIMaxZeroZero : FullKernelSKY.E :=
  .sort (.imax .zero .zero)

def sortMaxZeroZero : FullKernelSKY.E :=
  .sort (.max .zero .zero)

def natConst : FullKernelSKY.E :=
  .const 0 []

def runProbe (label : String) (e : FullKernelSKY.E) : IO Unit := do
  let some predC := FullKernelSKY.exprIsSortZeroComb?
    | throw <| IO.userError "failed to compile exprIsSortZero"
  let some eC := FullKernelSKY.compileExprNatUnitWithMode? .classic e
    | throw <| IO.userError s!"failed to compile expr for {label}"
  let out := Comb.app predC eC
  let decoded := SKYExec.decodeChurchBoolFuel 400000 out
  IO.println s!"{label}={repr decoded}"

def main (_args : List String) : IO UInt32 := do
  runProbe "sortZero" sortZero
  runProbe "sortOne" sortOne
  runProbe "sortIMaxZeroZero" sortIMaxZeroZero
  runProbe "sortMaxZeroZero" sortMaxZeroZero
  runProbe "natConst" natConst
  pure 0
