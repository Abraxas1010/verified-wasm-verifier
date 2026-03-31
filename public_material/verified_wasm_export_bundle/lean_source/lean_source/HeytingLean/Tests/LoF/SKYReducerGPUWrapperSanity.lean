import HeytingLean.LoF.Combinators.SKYReducerGPUWrapper

namespace HeytingLean
namespace Tests
namespace LoF
namespace SKYReducerGPUWrapperSanity

open HeytingLean.LoF.Combinators.SKYReducerKernel
open HeytingLean.LoF.Combinators.SKYReducerGPUWrapper

abbrev KernelState := HeytingLean.LoF.Combinators.SKYReducerKernel.State

def appState : KernelState :=
  { tags := #[NodeTag.code .combK, NodeTag.code .combS, NodeTag.code .app]
    lhs := #[0, 0, 0]
    rhs := #[0, 0, 1]
    oracleRefs := #[0, 0, 0]
    focus := 2
    stack := []
    maxNodes := 8 }

def kState : KernelState :=
  { tags := #[NodeTag.code .combK]
    lhs := #[0]
    rhs := #[0]
    oracleRefs := #[0]
    focus := 0
    stack := [7, 8]
    maxNodes := 8 }

def sState : KernelState :=
  { tags := #[NodeTag.code .combS]
    lhs := #[0]
    rhs := #[0]
    oracleRefs := #[0]
    focus := 0
    stack := [1, 2, 3]
    maxNodes := 8 }

def yState : KernelState :=
  { tags := #[NodeTag.code .combY]
    lhs := #[0]
    rhs := #[0]
    oracleRefs := #[0]
    focus := 0
    stack := [5]
    maxNodes := 8 }

def oracleState : KernelState :=
  { tags := #[NodeTag.code .oracle]
    lhs := #[0]
    rhs := #[0]
    oracleRefs := #[0]
    focus := 0
    stack := [11, 12]
    maxNodes := 8 }

def invalidFocusState : KernelState :=
  { oracleState with focus := 4 }

def wrappedStep? (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × KernelState) := do
  let wrapped ← ofKernelState? s
  let (status, wrapped') ← step? (oracleArrayEval oracleVals) wrapped
  let out ← toKernelState? wrapped'
  pure (status, out)

def wrappedRunFuel? (fuel : Nat) (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × KernelState) := do
  let wrapped ← ofKernelState? s
  let (status, wrapped') ← runFuel? (oracleArrayEval oracleVals) fuel wrapped
  let out ← toKernelState? wrapped'
  pure (status, out)

def expected? (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × KernelState) :=
  let r := step (oracleArrayEval oracleVals) s
  some (r.status, r.state)

def expectedRunFuel? (fuel : Nat) (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × KernelState) :=
  let r := runFuel (oracleArrayEval oracleVals) fuel s
  some (r.status, r.state)

example : Option.bind (ofKernelState? appState) toKernelState? = some appState := by
  native_decide

example : Option.bind (ofKernelState? kState) toKernelState? = some kState := by
  native_decide

example : Option.bind (ofKernelState? sState) toKernelState? = some sState := by
  native_decide

example : Option.bind (ofKernelState? yState) toKernelState? = some yState := by
  native_decide

example : Option.bind (ofKernelState? oracleState) toKernelState? = some oracleState := by
  native_decide

example : wrappedStep? appState #[] = expected? appState #[] := by
  native_decide

example : wrappedStep? kState #[] = expected? kState #[] := by
  native_decide

example : wrappedStep? sState #[] = expected? sState #[] := by
  native_decide

example : wrappedStep? yState #[] = expected? yState #[] := by
  native_decide

example : wrappedStep? oracleState #[1] = expected? oracleState #[1] := by
  native_decide

example : wrappedStep? oracleState #[0] = expected? oracleState #[0] := by
  native_decide

example : wrappedStep? invalidFocusState #[] = expected? invalidFocusState #[] := by
  native_decide

example : wrappedRunFuel? 2 appState #[] = expectedRunFuel? 2 appState #[] := by
  native_decide

example : wrappedRunFuel? 3 sState #[] = expectedRunFuel? 3 sState #[] := by
  native_decide

example : wrappedRunFuel? 2 yState #[] = expectedRunFuel? 2 yState #[] := by
  native_decide

example : wrappedRunFuel? 2 oracleState #[1] = expectedRunFuel? 2 oracleState #[1] := by
  native_decide

example : wrappedRunFuel? 1 invalidFocusState #[] = expectedRunFuel? 1 invalidFocusState #[] := by
  native_decide

end SKYReducerGPUWrapperSanity
end LoF
end Tests
end HeytingLean
