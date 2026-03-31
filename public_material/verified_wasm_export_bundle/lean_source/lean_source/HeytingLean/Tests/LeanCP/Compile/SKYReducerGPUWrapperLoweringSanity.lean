import HeytingLean.LeanCP.Compile.SKYLowering
import HeytingLean.LeanCP.Compile.SKYLoweringSemantics
import HeytingLean.LeanCP.Lang.CSemantics
import HeytingLean.LoF.Combinators.SKYReducerGPUWrapper

namespace HeytingLean
namespace Tests
namespace LeanCP
namespace Compile
namespace SKYReducerGPUWrapperLoweringSanity

open HeytingLean.LeanCP
open HeytingLean.LoF.Combinators.SKYReducerKernel
open HeytingLean.LoF.Combinators.SKYReducerGPUWrapper

abbrev KernelState := HeytingLean.LoF.Combinators.SKYReducerKernel.State

def wrapperLayout (s : WrapperState) (oracleVals : Array Int) :
    HeytingLean.LeanCP.Compile.SKYLoweringSemantics.ExecLayout :=
  HeytingLean.LeanCP.Compile.SKYLoweringSemantics.layoutFor s.maxNodes oracleVals.size (s.maxNodes + 1)

def writeIntList (heap : Heap) (base : Nat) (xs : List Int) : Heap :=
  match xs with
  | [] => heap
  | x :: rest => writeIntList (heap.write base (.int x)) (base + 1) rest

def writeNatList (heap : Heap) (base : Nat) (xs : List Nat) : Heap :=
  match xs with
  | [] => heap
  | x :: rest => writeNatList (heap.write base (.int (Int.ofNat x))) (base + 1) rest

def initExecState (s : WrapperState) (oracleVals : Array Int) : CState :=
  let layout := wrapperLayout s oracleVals
  let heap0 := Heap.empty
  let heap1 := writeIntList heap0 layout.tagsBase s.tags.toList
  let heap2 := writeNatList heap1 layout.lhsBase s.lhs.toList
  let heap3 := writeNatList heap2 layout.rhsBase s.rhs.toList
  let heap4 := writeNatList heap3 layout.refsBase s.oracleRefs.toList
  let heap5 := writeIntList heap4 layout.oracleValsBase oracleVals.toList
  let heap6 := writeNatList heap5 layout.stackBase s.stackData.toList
  let heap7 := heap6.write layout.focusBase (.int (Int.ofNat s.focus))
  let heap8 := heap7.write layout.stackSizeBase (.int (Int.ofNat s.stackSize))
  let heap9 := heap8.write layout.nodeCountBase (.int (Int.ofNat s.nodeCount))
  { heap := heap9
    env :=
      [ ("tags", .ptr 0 (Int.ofNat layout.tagsBase))
      , ("lhs", .ptr 0 (Int.ofNat layout.lhsBase))
      , ("rhs", .ptr 0 (Int.ofNat layout.rhsBase))
      , ("oracleRefs", .ptr 0 (Int.ofNat layout.refsBase))
      , ("oracleValues", .ptr 0 (Int.ofNat layout.oracleValsBase))
      , ("stack", .ptr 0 (Int.ofNat layout.stackBase))
      , ("focusPtr", .ptr 0 (Int.ofNat layout.focusBase))
      , ("stackSizePtr", .ptr 0 (Int.ofNat layout.stackSizeBase))
      , ("nodeCountPtr", .ptr 0 (Int.ofNat layout.nodeCountBase))
      , ("maxNodes", .int (Int.ofNat s.maxNodes)) ]
    nextAddr := 1000 }

def readIntCell? (heap : Heap) (addr : Nat) : Option Int := do
  match heap.read addr with
  | some (.int n) => some n
  | _ => none

def readNatCell? (heap : Heap) (addr : Nat) : Option Nat := do
  let n ← readIntCell? heap addr
  if _h : 0 ≤ n then
    some (Int.toNat n)
  else
    none

def readIntArray? (heap : Heap) (base count : Nat) : Option (Array Int) := do
  let vals ← (List.range count).mapM fun i => readIntCell? heap (base + i)
  pure vals.toArray

def readNatArray? (heap : Heap) (base count : Nat) : Option (Array Nat) := do
  let vals ← (List.range count).mapM fun i => readNatCell? heap (base + i)
  pure vals.toArray

def readWrapperState? (layout : HeytingLean.LeanCP.Compile.SKYLoweringSemantics.ExecLayout)
    (maxNodes : Nat) (st : CState) : Option WrapperState := do
  let focus ← readNatCell? st.heap layout.focusBase
  let stackSize ← readNatCell? st.heap layout.stackSizeBase
  let nodeCount ← readNatCell? st.heap layout.nodeCountBase
  let tags ← readIntArray? st.heap layout.tagsBase maxNodes
  let lhs ← readNatArray? st.heap layout.lhsBase maxNodes
  let rhs ← readNatArray? st.heap layout.rhsBase maxNodes
  let oracleRefs ← readNatArray? st.heap layout.refsBase maxNodes
  let stackData ← readNatArray? st.heap layout.stackBase maxNodes
  pure
    { tags := tags
      lhs := lhs
      rhs := rhs
      oracleRefs := oracleRefs
      stackData := stackData
      focus := focus
      stackSize := stackSize
      nodeCount := nodeCount
      maxNodes := maxNodes }

def runLoweredWrapper? (s : WrapperState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let layout := wrapperLayout s oracleVals
  match ← execStmt 400 HeytingLean.LeanCP.Compile.SKYLowering.skyReducerStepDecl.body
      (initExecState s oracleVals) with
  | .returned (.int code) st =>
      let status ← StepStatus.ofCode? code
      let outState ← readWrapperState? layout s.maxNodes st
      let normalized ← normalize? outState
      pure (status, normalized)
  | _ => none

def runLoweredWrapperFuel? (fuel : Nat) (s : WrapperState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) :=
  match fuel with
  | 0 => some (.halted, s)
  | fuel + 1 =>
      match runLoweredWrapper? s oracleVals with
      | some (.progress, s') => runLoweredWrapperFuel? fuel s' oracleVals
      | some result => some result
      | none => none

def appState : KernelState :=
  { tags := #[NodeTag.code .combK, NodeTag.code .combS, NodeTag.code .app]
    lhs := #[0, 0, 0]
    rhs := #[0, 0, 1]
    oracleRefs := #[0, 0, 0]
    focus := 2
    stack := []
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

def packedStep? (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let packed ← ofKernelState? s
  step? (oracleArrayEval oracleVals) packed

def packedRunFuel? (fuel : Nat) (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let packed ← ofKernelState? s
  runFuel? (oracleArrayEval oracleVals) fuel packed

example : runLoweredWrapper? (Option.getD (ofKernelState? appState) default) #[] =
    packedStep? appState #[] := by
  native_decide

example : runLoweredWrapper? (Option.getD (ofKernelState? sState) default) #[] =
    packedStep? sState #[] := by
  native_decide

example : runLoweredWrapper? (Option.getD (ofKernelState? yState) default) #[] =
    packedStep? yState #[] := by
  native_decide

example : runLoweredWrapper? (Option.getD (ofKernelState? oracleState) default) #[1] =
    packedStep? oracleState #[1] := by
  native_decide

example : runLoweredWrapper? (Option.getD (ofKernelState? invalidFocusState) default) #[] =
    packedStep? invalidFocusState #[] := by
  native_decide

example : runLoweredWrapperFuel? 2 (Option.getD (ofKernelState? appState) default) #[] =
    packedRunFuel? 2 appState #[] := by
  native_decide

example : runLoweredWrapperFuel? 3 (Option.getD (ofKernelState? sState) default) #[] =
    packedRunFuel? 3 sState #[] := by
  native_decide

example : runLoweredWrapperFuel? 2 (Option.getD (ofKernelState? yState) default) #[] =
    packedRunFuel? 2 yState #[] := by
  native_decide

example : runLoweredWrapperFuel? 2 (Option.getD (ofKernelState? oracleState) default) #[1] =
    packedRunFuel? 2 oracleState #[1] := by
  native_decide

example : runLoweredWrapperFuel? 1 (Option.getD (ofKernelState? invalidFocusState) default) #[] =
    packedRunFuel? 1 invalidFocusState #[] := by
  native_decide

end SKYReducerGPUWrapperLoweringSanity
end Compile
end LeanCP
end Tests
end HeytingLean
