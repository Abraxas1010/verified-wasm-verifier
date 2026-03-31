import HeytingLean.LoF.LeanKernel.FullKernelSKY

open HeytingLean.LoF.LeanKernel

def sortZero : FullKernelSKY.E :=
  .sort .zero

def main (_args : List String) : IO UInt32 := do
  let some k := FullKernelSKY.compileFullWithMode? .classic
    | throw <| IO.userError "failed to compile full kernel bundle"
  let result :=
    FullKernelSKY.runIsDefEqFullFuelWith k 20 400000 k.emptyEnv k.emptyRules sortZero sortZero
  IO.println s!"sort0_defeq_sort0={repr result}"
  pure 0
