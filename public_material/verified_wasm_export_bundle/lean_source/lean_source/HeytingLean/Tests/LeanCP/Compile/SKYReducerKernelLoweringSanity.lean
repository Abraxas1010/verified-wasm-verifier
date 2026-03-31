import HeytingLean.LeanCP.Compile.SKYLoweringSemantics

namespace HeytingLean
namespace Tests
namespace LeanCP
namespace Compile
namespace SKYReducerKernelLoweringSanity

open HeytingLean.LeanCP
open HeytingLean.LoF.Combinators.SKYReducerKernel
open HeytingLean.LeanCP.Compile.SKYLoweringSemantics

def appState : State :=
  { tags := #[NodeTag.code .combK, NodeTag.code .combS, NodeTag.code .app]
    lhs := #[0, 0, 0]
    rhs := #[0, 0, 1]
    oracleRefs := #[0, 0, 0]
    focus := 2
    stack := []
    maxNodes := 8 }

def kState : State :=
  { tags := #[NodeTag.code .combK]
    lhs := #[0]
    rhs := #[0]
    oracleRefs := #[0]
    focus := 0
    stack := [7, 8]
    maxNodes := 8 }

def sState : State :=
  { tags := #[NodeTag.code .combS]
    lhs := #[0]
    rhs := #[0]
    oracleRefs := #[0]
    focus := 0
    stack := [1, 2, 3]
    maxNodes := 8 }

def yState : State :=
  { tags := #[NodeTag.code .combY]
    lhs := #[0]
    rhs := #[0]
    oracleRefs := #[0]
    focus := 0
    stack := [5]
    maxNodes := 8 }

def oracleState : State :=
  { tags := #[NodeTag.code .oracle]
    lhs := #[0]
    rhs := #[0]
    oracleRefs := #[0]
    focus := 0
    stack := [11, 12]
    maxNodes := 8 }

def oracleMissingRefState : State :=
  { tags := #[NodeTag.code .oracle]
    lhs := #[0]
    rhs := #[0]
    oracleRefs := #[1]
    focus := 0
    stack := [11, 22]
    maxNodes := 8 }

def sOutOfHeapState : State :=
  { sState with maxNodes := 1 }

example :
    decodeKernelState? appState.maxNodes (layoutForState appState #[]) (encodeExecState appState #[]) =
      some appState := by
  native_decide

example :
    decodeKernelState? oracleState.maxNodes (layoutForState oracleState #[1])
      (encodeExecState oracleState #[1]) = some oracleState := by
  native_decide

example : runLoweredStep? appState #[] = expectedStep? appState #[] := by
  native_decide

example : runLoweredStep? kState #[] = expectedStep? kState #[] := by
  native_decide

example : runLoweredStep? sState #[] = expectedStep? sState #[] := by
  native_decide

example : runLoweredStep? yState #[] = expectedStep? yState #[] := by
  native_decide

example : runLoweredStep? oracleState #[1] = expectedStep? oracleState #[1] := by
  native_decide

example : runLoweredStep? oracleState #[0] = expectedStep? oracleState #[0] := by
  native_decide

example : runLoweredStep? oracleMissingRefState #[] = expectedStep? oracleMissingRefState #[] := by
  native_decide

example : runLoweredStep? sOutOfHeapState #[] = expectedStep? sOutOfHeapState #[] := by
  native_decide

example : runLoweredFuel? 2 appState #[] = expectedRunFuel? 2 appState #[] := by
  native_decide

example : runLoweredFuel? 3 sState #[] = expectedRunFuel? 3 sState #[] := by
  native_decide

example : runLoweredFuel? 2 yState #[] = expectedRunFuel? 2 yState #[] := by
  native_decide

example : runLoweredFuel? 2 oracleState #[1] = expectedRunFuel? 2 oracleState #[1] := by
  native_decide

example : runLoweredFuel? 1 sOutOfHeapState #[] = expectedRunFuel? 1 sOutOfHeapState #[] := by
  native_decide

end SKYReducerKernelLoweringSanity
end Compile
end LeanCP
end Tests
end HeytingLean
