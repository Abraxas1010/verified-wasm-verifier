import HeytingLean.LeanCP.Compile.SKYLowering
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Lang.CSemantics

/-!
# SKYLoweringSemantics

Executable correspondence helpers for the lowered SKY reducer kernel.

This module makes the proof-to-code map explicit:

- encode `SKYReducerKernel.State` into the raw C heap/env layout
- run the lowered LeanCP C body
- decode the resulting heap/env back into a kernel state

The higher-level simulation theorem chain still remains to be proved, but these
definitions keep the operational correspondence in a reusable Lean-owned
surface instead of burying it inside a sanity test.
-/

namespace HeytingLean
namespace LeanCP
namespace Compile
namespace SKYLoweringSemantics

open HeytingLean.LeanCP
open HeytingLean.LoF.Combinators.SKYReducerKernel

set_option maxHeartbeats 800000

structure ExecLayout where
  tagsBase : Nat
  lhsBase : Nat
  rhsBase : Nat
  refsBase : Nat
  oracleValsBase : Nat
  stackBase : Nat
  focusBase : Nat
  stackSizeBase : Nat
  nodeCountBase : Nat
  deriving DecidableEq, Repr, Inhabited

def layoutFor (nodeSlots oracleSlots stackSlots : Nat) : ExecLayout :=
  let tagsBase := 0
  let lhsBase := tagsBase + nodeSlots
  let rhsBase := lhsBase + nodeSlots
  let refsBase := rhsBase + nodeSlots
  let oracleValsBase := refsBase + nodeSlots
  let stackBase := oracleValsBase + oracleSlots
  let focusBase := stackBase + stackSlots
  let stackSizeBase := focusBase + 1
  let nodeCountBase := stackSizeBase + 1
  { tagsBase := tagsBase
    lhsBase := lhsBase
    rhsBase := rhsBase
    refsBase := refsBase
    oracleValsBase := oracleValsBase
    stackBase := stackBase
    focusBase := focusBase
    stackSizeBase := stackSizeBase
    nodeCountBase := nodeCountBase }

def oracleSlotCount (s : State) (oracleVals : Array Int) : Nat :=
  s.oracleRefs.foldl (fun acc ref => max acc (ref + 1)) oracleVals.size

def oracleValuesPadded (s : State) (oracleVals : Array Int) : List Int :=
  (List.range (oracleSlotCount s oracleVals)).map fun i => (oracleVals[i]?).getD 0

def layoutForState (s : State) (oracleVals : Array Int) : ExecLayout :=
  layoutFor s.maxNodes (oracleSlotCount s oracleVals) (s.stack.length + 1)

def writeIntList (heap : Heap) (base : Nat) (xs : List Int) : Heap :=
  match xs with
  | [] => heap
  | x :: rest => writeIntList (heap.write base (.int x)) (base + 1) rest

def writeNatList (heap : Heap) (base : Nat) (xs : List Nat) : Heap :=
  match xs with
  | [] => heap
  | x :: rest => writeNatList (heap.write base (.int (Int.ofNat x))) (base + 1) rest

theorem writeNatList_append (heap : Heap) (base : Nat) (xs ys : List Nat) :
    writeNatList heap base (xs ++ ys) =
      writeNatList (writeNatList heap base xs) (base + xs.length) ys := by
  induction xs generalizing heap base with
  | nil =>
      simp [writeNatList]
  | cons x xs ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (heap := heap.write base (.int (Int.ofNat x))) (base := base + 1)

theorem writeIntList_append (heap : Heap) (base : Nat) (xs ys : List Int) :
    writeIntList heap base (xs ++ ys) =
      writeIntList (writeIntList heap base xs) (base + xs.length) ys := by
  induction xs generalizing heap base with
  | nil =>
      simp [writeIntList]
  | cons x xs ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (heap := heap.write base (.int x)) (base := base + 1)

theorem array_toArray_append_one_eq_push {α : Type} (xs : Array α) (a : α) :
    (xs.toList ++ [a]).toArray = xs.push a := by
  apply (Array.toList_inj).mp
  simp [Array.toList_push]

theorem array_toArray_append_two_eq_push_push {α : Type} (xs : Array α) (a b : α) :
    (xs.toList ++ [a, b]).toArray = (xs.push a).push b := by
  apply (Array.toList_inj).mp
  simp [Array.toList_push]

theorem array_toArray_append_three_eq_push_push_push {α : Type} (xs : Array α) (a b c : α) :
    (xs.toList ++ [a, b, c]).toArray = ((xs.push a).push b).push c := by
  apply (Array.toList_inj).mp
  simp [Array.toList_push]

theorem oracleValuesPadded_length (s : State) (oracleVals : Array Int) :
    (oracleValuesPadded s oracleVals).length = oracleSlotCount s oracleVals := by
  simp [oracleValuesPadded]

theorem List.foldl_max_succ_ge_acc (xs : List Nat) (acc : Nat) :
    acc ≤ xs.foldl (fun cur ref => max cur (ref + 1)) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      exact le_trans (Nat.le_max_left _ _) (ih _)

theorem List.le_foldl_max_succ_of_mem (xs : List Nat) (acc x : Nat) (hmem : x ∈ xs) :
    x + 1 ≤ xs.foldl (fun cur ref => max cur (ref + 1)) acc := by
  induction xs generalizing acc with
  | nil =>
      cases hmem
  | cons y ys ih =>
      simp at hmem
      cases hmem with
      | inl hxy =>
          subst hxy
          exact le_trans (Nat.le_max_right _ _) (List.foldl_max_succ_ge_acc ys _)
      | inr hmem =>
          simpa using ih (acc := max acc (y + 1)) hmem

theorem oracleRef_lt_oracleSlotCount
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    s.oracleRefs[s.focus]'(by
      rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
      simpa [hrefs] using hfocus) < oracleSlotCount s oracleVals := by
  have hmem :
      s.oracleRefs[s.focus]'(by
        rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
        simpa [hrefs] using hfocus) ∈ s.oracleRefs.toList := by
    simpa using
      (Array.getElem_mem_toList (xs := s.oracleRefs) (i := s.focus)
        (by
          rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
          simpa [hrefs] using hfocus))
  have hle :=
    List.le_foldl_max_succ_of_mem s.oracleRefs.toList oracleVals.size
      (s.oracleRefs[s.focus]'(by
        rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
        simpa [hrefs] using hfocus)) hmem
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (by simpa [oracleSlotCount] using hle)

def encodeNodeArraysWithLayout (layout : ExecLayout) (s : State) : Heap :=
  let heap0 := Heap.empty
  let heap1 := writeIntList heap0 layout.tagsBase s.tags.toList
  let heap2 := writeNatList heap1 layout.lhsBase s.lhs.toList
  let heap3 := writeNatList heap2 layout.rhsBase s.rhs.toList
  writeNatList heap3 layout.refsBase s.oracleRefs.toList

def encodeOracleValuesWithLayout (layout : ExecLayout) (s : State) (oracleVals : Array Int) : Heap :=
  writeIntList (encodeNodeArraysWithLayout layout s) layout.oracleValsBase (oracleValuesPadded s oracleVals)

def encodeStackWithLayout (layout : ExecLayout) (s : State) (oracleVals : Array Int) : Heap :=
  writeNatList (encodeOracleValuesWithLayout layout s oracleVals) layout.stackBase s.stack.reverse

def encodeHeapWithLayout (layout : ExecLayout) (s : State) (oracleVals : Array Int) : Heap :=
  let heap6 := encodeStackWithLayout layout s oracleVals
  let heap7 := heap6.write layout.focusBase (.int (Int.ofNat s.focus))
  let heap8 := heap7.write layout.stackSizeBase (.int (Int.ofNat s.stack.length))
  heap8.write layout.nodeCountBase (.int (Int.ofNat s.nodeCount))

def encodeExecStateWithLayout (layout : ExecLayout) (s : State) (oracleVals : Array Int) : CState :=
  { heap := encodeHeapWithLayout layout s oracleVals
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

def encodeExecState (s : State) (oracleVals : Array Int) : CState :=
  encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals

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

def readIntList? (heap : Heap) (base count : Nat) : Option (List Int) :=
  match count with
  | 0 => some []
  | count + 1 => do
      let x ← readIntCell? heap base
      let xs ← readIntList? heap (base + 1) count
      pure (x :: xs)

def readNatList? (heap : Heap) (base count : Nat) : Option (List Nat) :=
  match count with
  | 0 => some []
  | count + 1 => do
      let x ← readNatCell? heap base
      let xs ← readNatList? heap (base + 1) count
      pure (x :: xs)

def readIntArray? (heap : Heap) (base count : Nat) : Option (Array Int) := do
  let vals ← readIntList? heap base count
  pure vals.toArray

def readNatArray? (heap : Heap) (base count : Nat) : Option (Array Nat) := do
  let vals ← readNatList? heap base count
  pure vals.toArray

def decodeKernelState? (maxNodes : Nat) (layout : ExecLayout) (st : CState) : Option State := do
  let focus ← readNatCell? st.heap layout.focusBase
  let stackSize ← readNatCell? st.heap layout.stackSizeBase
  let nodeCount ← readNatCell? st.heap layout.nodeCountBase
  let tags ← readIntArray? st.heap layout.tagsBase nodeCount
  let lhs ← readNatArray? st.heap layout.lhsBase nodeCount
  let rhs ← readNatArray? st.heap layout.rhsBase nodeCount
  let oracleRefs ← readNatArray? st.heap layout.refsBase nodeCount
  let stackCells ← readNatArray? st.heap layout.stackBase stackSize
  pure
    { tags := tags
      lhs := lhs
      rhs := rhs
      oracleRefs := oracleRefs
      focus := focus
      stack := stackCells.toList.reverse
      maxNodes := maxNodes }

def oracleArrayEval (vals : Array Int) (ref : Nat) : Bool :=
  match vals[ref]? with
  | some n => n ≠ 0
  | none => false

theorem oracleArrayEval_eq_getD_ne_zero (vals : Array Int) (ref : Nat) :
    oracleArrayEval vals ref = (((vals[ref]?).getD 0) ≠ 0) := by
  unfold oracleArrayEval
  split <;> simp [*]

def expectedStep? (s : State) (oracleVals : Array Int) : Option (StepStatus × State) :=
  let r := step (oracleArrayEval oracleVals) s
  some (r.status, r.state)

def runLoweredStep? (s : State) (oracleVals : Array Int) : Option (StepStatus × State) := do
  let layout := layoutForState s oracleVals
  match ← execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout layout s oracleVals) with
  | .returned (.int code) st =>
      let status ← StepStatus.ofCode? code
      let outState ← decodeKernelState? s.maxNodes layout st
      pure (status, outState)
  | _ => none

def runLoweredFuel? (fuel : Nat) (s : State) (oracleVals : Array Int) :
    Option (StepStatus × State) :=
  match fuel with
  | 0 => some (.halted, s)
  | fuel + 1 =>
      match runLoweredStep? s oracleVals with
      | some (.progress, s') => runLoweredFuel? fuel s' oracleVals
      | some result => some result
      | none => none

def expectedRunFuel? (fuel : Nat) (s : State) (oracleVals : Array Int) :
    Option (StepStatus × State) :=
  let r := runFuel (oracleArrayEval oracleVals) fuel s
  some (r.status, r.state)

def skyReducerLocals : List (String × CType) :=
  [ ("tag", .int)
  , ("focus", .int)
  , ("stackSize", .int)
  , ("nodeCount", .int)
  , ("x", .int)
  , ("y", .int)
  , ("z", .int)
  , ("ref", .int) ]

def skyReducerEntry (s : State) (oracleVals : Array Int) : CState :=
  enterBlockState (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) skyReducerLocals

def skyReducerFocusLoadedState (s : State) (oracleVals : Array Int) : CState :=
  (skyReducerEntry s oracleVals).updateVar "focus" (.int (Int.ofNat s.focus))

def skyReducerStackSizeLoadedState (s : State) (oracleVals : Array Int) : CState :=
  (skyReducerFocusLoadedState s oracleVals).updateVar "stackSize" (.int (Int.ofNat s.stack.length))

def skyReducerScalarsLoadedState (s : State) (oracleVals : Array Int) : CState :=
  (skyReducerStackSizeLoadedState s oracleVals).updateVar "nodeCount" (.int (Int.ofNat s.nodeCount))

def skyReducerAppTagLoadedState (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    CState :=
  (skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))

def skyReducerAppXVal (s : State) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) : CVal :=
  .int (Int.ofNat (s.rhs[s.focus]'(by
    rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
    simpa [hrhs] using hfocus)))

def skyReducerAppXLoadedState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerAppTagLoadedState s oracleVals hfocus).updateVar "x" (skyReducerAppXVal s hwf hfocus)

def skyReducerAppStoredState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerAppXLoadedState s oracleVals hwf hfocus).withHeap
    ((skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.write
      ((layoutForState s oracleVals).stackBase + s.stack.length)
      (skyReducerAppXVal s hwf hfocus))

def skyReducerAppFocusVal (s : State) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) : CVal :=
  .int (Int.ofNat (s.lhs[s.focus]'(by
    rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
    simpa [hlhs] using hfocus)))

def skyReducerAppFocusUpdatedState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerAppStoredState s oracleVals hwf hfocus).updateVar "focus" (skyReducerAppFocusVal s hwf hfocus)

def skyReducerAppStackSizeUpdatedState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus).updateVar "stackSize"
    (.int (Int.ofNat (s.stack.length + 1)))

def skyReducerAppCommittedFocusState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).withHeap
    (((skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap).write
      (layoutForState s oracleVals).focusBase (skyReducerAppFocusVal s hwf hfocus))

def skyReducerAppCommittedStackSizeState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerAppCommittedFocusState s oracleVals hwf hfocus).withHeap
    (((skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap).write
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length + 1))))

def skyReducerAppCommittedState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).withHeap
    (((skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap).write
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount)))

def skyReducerKXVal (s : State) (hstack : 2 ≤ s.stack.length) : CVal :=
  .int (Int.ofNat (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩))

def skyReducerKXLoadedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CState :=
  (skyReducerAppTagLoadedState s oracleVals hfocus).updateVar "x" (skyReducerKXVal s hstack)

def skyReducerKFocusUpdatedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CState :=
  (skyReducerKXLoadedState s oracleVals hfocus hstack).updateVar "focus" (skyReducerKXVal s hstack)

def skyReducerKStackSizeUpdatedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CState :=
  (skyReducerKFocusUpdatedState s oracleVals hfocus hstack).updateVar "stackSize"
    (.int (Int.ofNat (s.stack.length - 2)))

def skyReducerKCommittedFocusState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CState :=
  (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).withHeap
    (((skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
      (layoutForState s oracleVals).focusBase (skyReducerKXVal s hstack))

def skyReducerKCommittedStackSizeState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CState :=
  (skyReducerKCommittedFocusState s oracleVals hfocus hstack).withHeap
    (((skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap).write
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2))))

def skyReducerKCommittedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CState :=
  (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).withHeap
    (((skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap).write
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount)))

def skyReducerYXVal (s : State) (hstack : 1 ≤ s.stack.length) : CVal :=
  .int (Int.ofNat (s.stack.get ⟨0, by omega⟩))

def skyReducerYSelfNat (s : State) : Nat :=
  s.nodeCount

def skyReducerYSelfVal (s : State) : CVal :=
  .int (Int.ofNat (skyReducerYSelfNat s))

def skyReducerYOutNat (s : State) : Nat :=
  s.nodeCount + 1

def skyReducerYOutVal (s : State) : CVal :=
  .int (Int.ofNat (skyReducerYOutNat s))

def skyReducerYXLoadedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerAppTagLoadedState s oracleVals hfocus).updateVar "x" (skyReducerYXVal s hstack)

def skyReducerYSelfTagStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYXLoadedState s oracleVals hfocus hstack).withHeap
    (((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).tagsBase + skyReducerYSelfNat s) (.int (NodeTag.code .app)))

def skyReducerYSelfLhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).lhsBase + skyReducerYSelfNat s) (.int (Int.ofNat s.focus)))

def skyReducerYSelfRhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).rhsBase + skyReducerYSelfNat s) (skyReducerYXVal s hstack))

def skyReducerYSelfRefStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).refsBase + skyReducerYSelfNat s) (.int 0))

def skyReducerYOutTagStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).tagsBase + skyReducerYOutNat s) (.int (NodeTag.code .app)))

def skyReducerYOutLhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYOutTagStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).lhsBase + skyReducerYOutNat s) (skyReducerYXVal s hstack))

def skyReducerYOutRhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYOutLhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).rhsBase + skyReducerYOutNat s) (skyReducerYSelfVal s))

def skyReducerYOutRefStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYOutRhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).refsBase + skyReducerYOutNat s) (.int 0))

def skyReducerYFocusUpdatedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYOutRefStoredState s oracleVals hfocus hstack).updateVar "focus" (skyReducerYOutVal s)

def skyReducerYNodeCountUpdatedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYFocusUpdatedState s oracleVals hfocus hstack).updateVar "nodeCount"
    (.int (Int.ofNat (s.nodeCount + 2)))

def skyReducerYStackSizeUpdatedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYNodeCountUpdatedState s oracleVals hfocus hstack).updateVar "stackSize"
    (.int (Int.ofNat (s.stack.length - 1)))

def skyReducerYCommittedFocusState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).withHeap
    (((skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
      (layoutForState s oracleVals).focusBase (skyReducerYOutVal s))

def skyReducerYCommittedStackSizeState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYCommittedFocusState s oracleVals hfocus hstack).withHeap
    (((skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap).write
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 1))))

def skyReducerYCommittedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length) : CState :=
  (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).withHeap
    (((skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap).write
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat (s.nodeCount + 2))))

def skyReducerYNextState (s : State) (hstack : 1 ≤ s.stack.length) : State :=
  { s with
      tags := (s.tags.push (NodeTag.code .app)).push (NodeTag.code .app)
      lhs := (s.lhs.push s.focus).push (s.stack.get ⟨0, by omega⟩)
      rhs := (s.rhs.push (s.stack.get ⟨0, by omega⟩)).push s.nodeCount
      oracleRefs := (s.oracleRefs.push 0).push 0
      focus := s.nodeCount + 1
      stack := s.stack.drop 1 }

def skyReducerYGroupedHeap (s : State) (oracleVals : Array Int)
    (hstack : 1 ≤ s.stack.length) : Heap :=
  let layout := layoutForState s oracleVals
  ((((((((encodeHeapWithLayout layout s oracleVals).write
      (layout.tagsBase + skyReducerYSelfNat s) (.int (NodeTag.code .app))).write
      (layout.tagsBase + skyReducerYOutNat s) (.int (NodeTag.code .app))).write
      (layout.lhsBase + skyReducerYSelfNat s) (.int (Int.ofNat s.focus))).write
      (layout.lhsBase + skyReducerYOutNat s) (skyReducerYXVal s hstack)).write
      (layout.rhsBase + skyReducerYSelfNat s) (skyReducerYXVal s hstack)).write
      (layout.rhsBase + skyReducerYOutNat s) (skyReducerYSelfVal s)).write
      (layout.refsBase + skyReducerYSelfNat s) (.int 0)).write
      (layout.refsBase + skyReducerYOutNat s) (.int 0)

def skyReducerSXVal (s : State) (hstack : 3 ≤ s.stack.length) : CVal :=
  .int (Int.ofNat (s.stack.get ⟨0, by omega⟩))

def skyReducerSYVal (s : State) (hstack : 3 ≤ s.stack.length) : CVal :=
  .int (Int.ofNat (s.stack.get ⟨1, by omega⟩))

def skyReducerSZVal (s : State) (hstack : 3 ≤ s.stack.length) : CVal :=
  .int (Int.ofNat (s.stack.get ⟨2, by omega⟩))

def skyReducerSNode0Nat (s : State) : Nat :=
  s.nodeCount

def skyReducerSNode0Val (s : State) : CVal :=
  .int (Int.ofNat (skyReducerSNode0Nat s))

def skyReducerSNode1Nat (s : State) : Nat :=
  s.nodeCount + 1

def skyReducerSNode1Val (s : State) : CVal :=
  .int (Int.ofNat (skyReducerSNode1Nat s))

def skyReducerSNode2Nat (s : State) : Nat :=
  s.nodeCount + 2

def skyReducerSNode2Val (s : State) : CVal :=
  .int (Int.ofNat (skyReducerSNode2Nat s))

def skyReducerSXLoadedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerAppTagLoadedState s oracleVals hfocus).updateVar "x" (skyReducerSXVal s hstack)

def skyReducerSXYLoadedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSXLoadedState s oracleVals hfocus hstack).updateVar "y" (skyReducerSYVal s hstack)

def skyReducerSXYZLoadedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSXYLoadedState s oracleVals hfocus hstack).updateVar "z" (skyReducerSZVal s hstack)

def skyReducerSNode0TagStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSXYZLoadedState s oracleVals hfocus hstack).withHeap
    (((skyReducerSXYZLoadedState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).tagsBase + skyReducerSNode0Nat s) (.int (NodeTag.code .app)))

def skyReducerSNode0LhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode0TagStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).lhsBase + skyReducerSNode0Nat s) (skyReducerSXVal s hstack))

def skyReducerSNode0RhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).rhsBase + skyReducerSNode0Nat s) (skyReducerSZVal s hstack))

def skyReducerSNode0RefStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).refsBase + skyReducerSNode0Nat s) (.int 0))

def skyReducerSNode1TagStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).tagsBase + skyReducerSNode1Nat s) (.int (NodeTag.code .app)))

def skyReducerSNode1LhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode1TagStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).lhsBase + skyReducerSNode1Nat s) (skyReducerSYVal s hstack))

def skyReducerSNode1RhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).rhsBase + skyReducerSNode1Nat s) (skyReducerSZVal s hstack))

def skyReducerSNode1RefStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).refsBase + skyReducerSNode1Nat s) (.int 0))

def skyReducerSNode2TagStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).tagsBase + skyReducerSNode2Nat s) (.int (NodeTag.code .app)))

def skyReducerSNode2LhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode2TagStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).lhsBase + skyReducerSNode2Nat s) (skyReducerSNode0Val s))

def skyReducerSNode2RhsStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).rhsBase + skyReducerSNode2Nat s) (skyReducerSNode1Val s))

def skyReducerSNode2RefStoredState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).withHeap
    (((skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap).write
      ((layoutForState s oracleVals).refsBase + skyReducerSNode2Nat s) (.int 0))

def skyReducerSFocusUpdatedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).updateVar "focus" (skyReducerSNode2Val s)

def skyReducerSNodeCountUpdatedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSFocusUpdatedState s oracleVals hfocus hstack).updateVar "nodeCount"
    (.int (Int.ofNat (s.nodeCount + 3)))

def skyReducerSStackSizeUpdatedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSNodeCountUpdatedState s oracleVals hfocus hstack).updateVar "stackSize"
    (.int (Int.ofNat (s.stack.length - 3)))

def skyReducerSCommittedFocusState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).withHeap
    (((skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
      (layoutForState s oracleVals).focusBase (skyReducerSNode2Val s))

def skyReducerSCommittedStackSizeState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSCommittedFocusState s oracleVals hfocus hstack).withHeap
    (((skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap).write
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 3))))

def skyReducerSCommittedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length) : CState :=
  (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).withHeap
    (((skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap).write
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat (s.nodeCount + 3))))

def skyReducerSNextState (s : State) (hstack : 3 ≤ s.stack.length) : State :=
  { s with
      tags := ((s.tags.push (NodeTag.code .app)).push (NodeTag.code .app)).push (NodeTag.code .app)
      lhs := ((s.lhs.push (s.stack.get ⟨0, by omega⟩)).push (s.stack.get ⟨1, by omega⟩)).push s.nodeCount
      rhs := ((s.rhs.push (s.stack.get ⟨2, by omega⟩)).push (s.stack.get ⟨2, by omega⟩)).push (s.nodeCount + 1)
      oracleRefs := ((s.oracleRefs.push 0).push 0).push 0
      focus := s.nodeCount + 2
      stack := s.stack.drop 3 }

def skyReducerSGroupedHeap (s : State) (oracleVals : Array Int)
    (hstack : 3 ≤ s.stack.length) : Heap :=
  let layout := layoutForState s oracleVals
  ((((((((((((encodeHeapWithLayout layout s oracleVals).write
      (layout.tagsBase + skyReducerSNode0Nat s) (.int (NodeTag.code .app))).write
      (layout.tagsBase + skyReducerSNode1Nat s) (.int (NodeTag.code .app))).write
      (layout.tagsBase + skyReducerSNode2Nat s) (.int (NodeTag.code .app))).write
      (layout.lhsBase + skyReducerSNode0Nat s) (skyReducerSXVal s hstack)).write
      (layout.lhsBase + skyReducerSNode1Nat s) (skyReducerSYVal s hstack)).write
      (layout.lhsBase + skyReducerSNode2Nat s) (skyReducerSNode0Val s)).write
      (layout.rhsBase + skyReducerSNode0Nat s) (skyReducerSZVal s hstack)).write
      (layout.rhsBase + skyReducerSNode1Nat s) (skyReducerSZVal s hstack)).write
      (layout.rhsBase + skyReducerSNode2Nat s) (skyReducerSNode1Val s)).write
      (layout.refsBase + skyReducerSNode0Nat s) (.int 0)).write
      (layout.refsBase + skyReducerSNode1Nat s) (.int 0)).write
      (layout.refsBase + skyReducerSNode2Nat s) (.int 0)

def skyReducerOracleXVal (s : State) (hstack : 2 ≤ s.stack.length) : CVal :=
  .int (Int.ofNat (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩))

def skyReducerOracleYVal (s : State) (hstack : 2 ≤ s.stack.length) : CVal :=
  .int (Int.ofNat (s.stack.get ⟨1, by omega⟩))

def skyReducerOracleRefVal (s : State) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) : CVal :=
  .int (Int.ofNat (s.oracleRefs[s.focus]'(by
    rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
    simpa [hrefs] using hfocus)))

def skyReducerOracleXLoadedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CState :=
  (skyReducerAppTagLoadedState s oracleVals hfocus).updateVar "x" (skyReducerOracleXVal s hstack)

def skyReducerOracleXYLoadedState (s : State) (oracleVals : Array Int)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CState :=
  (skyReducerOracleXLoadedState s oracleVals hfocus hstack).updateVar "y" (skyReducerOracleYVal s hstack)

def skyReducerOracleXYRefLoadedState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CState :=
  (skyReducerOracleXYLoadedState s oracleVals hfocus hstack).updateVar "ref"
    (skyReducerOracleRefVal s hwf hfocus)

def skyReducerOracleFocusUpdatedState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) : CState :=
  (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).updateVar "focus" target

def skyReducerOracleStackSizeUpdatedState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) : CState :=
  (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack target).updateVar "stackSize"
    (.int (Int.ofNat (s.stack.length - 2)))

def skyReducerOracleCommittedFocusState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) : CState :=
  (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target).withHeap
    (((skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target).heap).write
      (layoutForState s oracleVals).focusBase target)

def skyReducerOracleCommittedStackSizeState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) : CState :=
  (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack target).withHeap
    (((skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack target).heap).write
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2))))

def skyReducerOracleCommittedState (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) : CState :=
  (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack target).withHeap
    (((skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack target).heap).write
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount)))

def skyReducerOracleTargetNat (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : Nat :=
  let ref := s.oracleRefs[s.focus]'(by
    rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
    simpa [hrefs] using hfocus)
  if oracleArrayEval oracleVals ref then
    s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩
  else
    s.stack.get ⟨1, by omega⟩

def skyReducerOracleTargetVal (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) : CVal :=
  .int (Int.ofNat (skyReducerOracleTargetNat s oracleVals hwf hfocus hstack))

theorem evalExpr_deref_var_updateVar_ne
    (st : CState) (ptrVar x : String) (v : CVal) (hneq : ptrVar ≠ x) :
  evalExpr (.deref (.var ptrVar)) (st.updateVar x v) = evalExpr (.deref (.var ptrVar)) st := by
  simp [evalExpr, evalStaticExpr]
  rw [lookupVar_updateVar_ne st x ptrVar v hneq]
  cases hlookup : st.lookupVar ptrVar <;>
    simp [CState.updateVar, CState.findAllocByBlock, CState.readPtr, CState.resolvePtr, CState.readCell]

theorem execStmt_writeScalar_block0_of_lookups
    (fuel : Nat) (st : CState) (ptrName valName : String) (addr : Nat) (v : CVal)
    (hPtr : st.lookupVar ptrName = some (.ptr 0 (Int.ofNat addr)))
    (hVal : st.lookupVar valName = some v) :
    execStmt (fuel + 1) (SKYLowering.writeScalar ptrName (.var valName)) st =
      some (.normal (st.withHeap (st.heap.write addr v))) := by
  have hWrite :
      st.writePtr { block := 0, offset := Int.ofNat addr } v =
        some (st.withHeap (st.heap.write addr v)) := by
    simpa using (CState.writePtr_block0 st addr addr v)
  cases fuel <;>
    simp [SKYLowering.writeScalar, execStmt, evalExpr, evalStaticExpr, hPtr, hVal]
  · exact hWrite
  · exact hWrite

theorem execStmt_storeAt_block0_of_evals
    (fuel : Nat) (st : CState) (base : String) (idx value : CExpr) (addr : Nat) (v : CVal)
    (hAddr : evalExpr (.binop .add (.var base) idx) st = some (.ptr 0 (Int.ofNat addr)))
    (hVal : evalExpr value st = some v) :
    execStmt (fuel + 1) (SKYLowering.storeAt base idx value) st =
      some (.normal (st.withHeap (st.heap.write addr v))) := by
  have hWrite :
      st.writePtr { block := 0, offset := Int.ofNat addr } v =
        some (st.withHeap (st.heap.write addr v)) := by
    simpa using (CState.writePtr_block0 st addr addr v)
  cases fuel <;>
    simp [SKYLowering.storeAt, execStmt, hAddr, hVal]
  · exact hWrite
  · exact hWrite

theorem evalExpr_nodeIx_of_lookup
    (st : CState) (nodeCount : Nat) (offset : Nat)
    (hNodeCount : st.lookupVar "nodeCount" = some (.int (Int.ofNat nodeCount))) :
    evalExpr (SKYLowering.nodeIx offset) st =
      some (.int (Int.ofNat (nodeCount + offset))) := by
  have hnonneg : 0 ≤ (nodeCount : Int) + offset := by
    omega
  calc
    evalExpr (SKYLowering.nodeIx offset) st
      = evalBinOp .add (.int (Int.ofNat nodeCount)) (.int (Int.ofNat offset)) := by
          simp [SKYLowering.nodeIx, evalExpr, evalStaticExpr, hNodeCount]
    _ = some (.int (Int.ofNat (nodeCount + offset))) := by
          simpa [Int.ofNat_add] using
            (rfl :
              evalBinOp .add (.int (Int.ofNat nodeCount)) (.int (Int.ofNat offset)) =
                some (.int (Int.ofNat nodeCount + Int.ofNat offset)))

theorem evalExpr_basePlusNodeIx_of_lookups
    (st : CState) (baseName : String) (base nodeCount offset : Nat)
    (hBase : st.lookupVar baseName = some (.ptr 0 (Int.ofNat base)))
    (hNodeCount : st.lookupVar "nodeCount" = some (.int (Int.ofNat nodeCount))) :
    evalExpr (.binop .add (.var baseName) (SKYLowering.nodeIx offset)) st =
      some (.ptr 0 (Int.ofNat (base + nodeCount + offset))) := by
  have hIdx := evalExpr_nodeIx_of_lookup st nodeCount offset hNodeCount
  have hnonneg : 0 ≤ (base : Int) + (nodeCount + offset) := by
    omega
  calc
    evalExpr (.binop .add (.var baseName) (SKYLowering.nodeIx offset)) st
      = evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int (Int.ofNat (nodeCount + offset))) := by
          simp [evalExpr, evalStaticExpr, hBase, hIdx]
    _ = some (.ptr 0 (Int.ofNat (base + nodeCount + offset))) := by
          change
            (if 0 ≤ (base : Int) + (nodeCount + offset) then
              some (CVal.ptr 0 (Int.ofNat (base + (nodeCount + offset))))
            else none) =
              some (.ptr 0 (Int.ofNat (base + nodeCount + offset)))
          simp [hnonneg, Nat.add_assoc]

theorem execStmt_commitAndReturn_of_steps
    (code : StepStatus) (st stFocus stStack stDone : CState)
    (hFocus :
      execStmt 2 (SKYLowering.writeScalar "focusPtr" (.var "focus")) st =
        some (.normal stFocus))
    (hStack :
      execStmt 2 (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize")) stFocus =
        some (.normal stStack))
    (hNode :
      execStmt 2 (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount")) stStack =
        some (.normal stDone)) :
    execStmt 4 (SKYLowering.commitAndReturn code) st =
      some (.returned (.int code.code) stDone) := by
  calc
    execStmt 4 (SKYLowering.commitAndReturn code) st
      = execStmt 3
          (.seq
            (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
            (.seq
              (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
              (.ret (.intLit code.code))))
          stFocus := by
            exact execStmt_seq_of_normal 3
              (SKYLowering.writeScalar "focusPtr" (.var "focus"))
              (.seq
                (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
                (.seq
                  (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
                  (.ret (.intLit code.code))))
              st stFocus hFocus
    _ = execStmt 2
          (.seq
            (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
            (.ret (.intLit code.code)))
          stStack := by
            exact execStmt_seq_of_normal 2
              (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
              (.seq
                (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
                (.ret (.intLit code.code)))
              stFocus stStack hStack
    _ = execStmt 1 (.ret (.intLit code.code)) stDone := by
            exact execStmt_seq_of_normal 1
              (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
              (.ret (.intLit code.code))
              stStack stDone hNode
    _ = some (.returned (.int code.code) stDone) := by
          simp [execStmt, evalExpr, evalStaticExpr]

def committedFocusState (st : CState) (layout : ExecLayout) (focusVal : CVal) : CState :=
  st.withHeap (st.heap.write layout.focusBase focusVal)

def committedStackSizeState
    (st : CState) (layout : ExecLayout) (focusVal stackSizeVal : CVal) : CState :=
  (committedFocusState st layout focusVal).withHeap
    ((committedFocusState st layout focusVal).heap.write layout.stackSizeBase stackSizeVal)

def committedNodeCountState
    (st : CState) (layout : ExecLayout) (focusVal stackSizeVal nodeCountVal : CVal) : CState :=
  (committedStackSizeState st layout focusVal stackSizeVal).withHeap
    ((committedStackSizeState st layout focusVal stackSizeVal).heap.write
      layout.nodeCountBase nodeCountVal)

theorem execStmt_commitAndReturn_of_lookups
    (code : StepStatus) (st : CState) (layout : ExecLayout)
    (focusVal stackSizeVal nodeCountVal : CVal)
    (hFocusPtr : st.lookupVar "focusPtr" = some (.ptr 0 (Int.ofNat layout.focusBase)))
    (hFocus : st.lookupVar "focus" = some focusVal)
    (hStackPtr : st.lookupVar "stackSizePtr" = some (.ptr 0 (Int.ofNat layout.stackSizeBase)))
    (hStack : st.lookupVar "stackSize" = some stackSizeVal)
    (hNodePtr : st.lookupVar "nodeCountPtr" = some (.ptr 0 (Int.ofNat layout.nodeCountBase)))
    (hNode : st.lookupVar "nodeCount" = some nodeCountVal) :
    execStmt 4 (SKYLowering.commitAndReturn code) st =
      some (.returned (.int code.code)
        (committedNodeCountState st layout focusVal stackSizeVal nodeCountVal)) := by
  refine execStmt_commitAndReturn_of_steps code
    st
    (committedFocusState st layout focusVal)
    (committedStackSizeState st layout focusVal stackSizeVal)
    (committedNodeCountState st layout focusVal stackSizeVal nodeCountVal)
    ?_ ?_ ?_
  · simpa [committedFocusState] using
      (execStmt_writeScalar_block0_of_lookups 1 st "focusPtr" "focus"
        layout.focusBase focusVal hFocusPtr hFocus)
  · simpa [committedStackSizeState, committedFocusState] using
      (execStmt_writeScalar_block0_of_lookups 1
        (committedFocusState st layout focusVal) "stackSizePtr" "stackSize"
        layout.stackSizeBase stackSizeVal
        (by simpa [committedFocusState] using hStackPtr)
        (by simpa [committedFocusState] using hStack))
  · simpa [committedNodeCountState, committedStackSizeState, committedFocusState] using
      (execStmt_writeScalar_block0_of_lookups 1
        (committedStackSizeState st layout focusVal stackSizeVal) "nodeCountPtr" "nodeCount"
        layout.nodeCountBase nodeCountVal
        (by simpa [committedStackSizeState, committedFocusState] using hNodePtr)
        (by simpa [committedStackSizeState, committedFocusState] using hNode))

theorem skyReducerEntry_lookup_focusPtr (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "focusPtr")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_stackSizePtr (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "stackSizePtr")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_nodeCountPtr (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "nodeCountPtr")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_tags (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "tags" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).tagsBase)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "tags")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_lhs (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "lhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "lhs")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_rhs (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "rhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "rhs")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_stack (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "stack" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "stack")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_oracleRefs (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "oracleRefs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "oracleRefs")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_oracleValues (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "oracleValues" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).oracleValsBase)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "oracleValues")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_maxNodes (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "maxNodes" =
      some (.int (Int.ofNat s.maxNodes)) := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_ne
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "maxNodes")
      (hnot := by intro ty hmem; simp [skyReducerLocals] at hmem))

theorem skyReducerEntry_lookup_focus_undef (s : State) (oracleVals : Array Int) :
    (skyReducerEntry s oracleVals).lookupVar "focus" = some CVal.undef := by
  simpa [skyReducerEntry] using
    (lookupVar_enterBlockState_mem
      (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (decls := skyReducerLocals) (x := "focus") (ty := CType.int)
      (hmem := by simp [skyReducerLocals]))

theorem skyReducerEntry_eval_focusPtr (s : State) (oracleVals : Array Int) :
    evalExpr (.deref (.var "focusPtr")) (skyReducerEntry s oracleVals) = some (.int (Int.ofNat s.focus)) := by
  have hFocusStack :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).stackSizeBase := by
    intro h
    simp [layoutForState, layoutFor] at h
  have hFocusNode :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    intro h
    simp [layoutForState, layoutFor] at h
    omega
  simp [evalExpr, evalStaticExpr]
  rw [skyReducerEntry_lookup_focusPtr]
  simp [CState.readPtr, CState.resolvePtr, CState.readCell,
    skyReducerEntry, encodeExecStateWithLayout, encodeHeapWithLayout]
  rw [heap_read_write_ne _ _ _ _ hFocusNode]
  rw [heap_read_write_ne _ _ _ _ hFocusStack]
  rw [heap_read_write_eq]

theorem skyReducerEntry_eval_stackSizePtr (s : State) (oracleVals : Array Int) :
    evalExpr (.deref (.var "stackSizePtr")) (skyReducerEntry s oracleVals) =
      some (.int (Int.ofNat s.stack.length)) := by
  have hStackNode :
      (layoutForState s oracleVals).stackSizeBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    intro h
    simp [layoutForState, layoutFor] at h
  simp [evalExpr, evalStaticExpr]
  rw [skyReducerEntry_lookup_stackSizePtr]
  simp [CState.readPtr, CState.resolvePtr, CState.readCell,
    skyReducerEntry, encodeExecStateWithLayout, encodeHeapWithLayout]
  rw [heap_read_write_ne _ _ _ _ hStackNode]
  rw [heap_read_write_eq]

theorem skyReducerEntry_eval_nodeCountPtr (s : State) (oracleVals : Array Int) :
    evalExpr (.deref (.var "nodeCountPtr")) (skyReducerEntry s oracleVals) =
      some (.int (Int.ofNat s.nodeCount)) := by
  simp [evalExpr, evalStaticExpr]
  rw [skyReducerEntry_lookup_nodeCountPtr]
  simp [CState.readPtr, CState.resolvePtr, CState.readCell,
    skyReducerEntry, encodeExecStateWithLayout, encodeHeapWithLayout]
  rw [heap_read_write_eq]

theorem skyReducerFocusLoadedState_eval_stackSizePtr (s : State) (oracleVals : Array Int) :
    evalExpr (.deref (.var "stackSizePtr")) (skyReducerFocusLoadedState s oracleVals) =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerFocusLoadedState]
  rw [evalExpr_deref_var_updateVar_ne
    (st := skyReducerEntry s oracleVals) (ptrVar := "stackSizePtr")
    (x := "focus") (v := .int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_eval_stackSizePtr s oracleVals

theorem skyReducerStackSizeLoadedState_eval_nodeCountPtr (s : State) (oracleVals : Array Int) :
    evalExpr (.deref (.var "nodeCountPtr")) (skyReducerStackSizeLoadedState s oracleVals) =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerStackSizeLoadedState]
  rw [evalExpr_deref_var_updateVar_ne
    (st := skyReducerFocusLoadedState s oracleVals) (ptrVar := "nodeCountPtr")
    (x := "stackSize") (v := .int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [evalExpr_deref_var_updateVar_ne
    (st := skyReducerEntry s oracleVals) (ptrVar := "nodeCountPtr")
    (x := "focus") (v := .int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_eval_nodeCountPtr s oracleVals

theorem skyReducerScalarsLoadedState_lookup_focus (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "focus" =
      some (.int (Int.ofNat s.focus)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "focus" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focus" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  simpa using lookupVar_updateVar_eq (skyReducerEntry s oracleVals) "focus" (.int (Int.ofNat s.focus))

theorem skyReducerScalarsLoadedState_lookup_nodeCount (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerScalarsLoadedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerStackSizeLoadedState s oracleVals)
      "nodeCount" (.int (Int.ofNat s.nodeCount))

theorem skyReducerScalarsLoadedState_lookup_stackSize (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "stackSize" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerFocusLoadedState s oracleVals)
      "stackSize" (.int (Int.ofNat s.stack.length))

theorem skyReducerScalarsLoadedState_lookup_focusPtr (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "focusPtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focusPtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "focusPtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_focusPtr s oracleVals

theorem skyReducerScalarsLoadedState_lookup_stackSizePtr (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "stackSizePtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stackSizePtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "stackSizePtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_stackSizePtr s oracleVals

theorem skyReducerScalarsLoadedState_lookup_nodeCountPtr (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "nodeCountPtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCountPtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCountPtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_nodeCountPtr s oracleVals

theorem skyReducerScalarsLoadedState_lookup_tags (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "tags" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).tagsBase)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "tags" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "tags" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "tags" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_tags s oracleVals

theorem skyReducerScalarsLoadedState_lookup_lhs (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "lhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "lhs" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "lhs" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "lhs" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_lhs s oracleVals

theorem skyReducerScalarsLoadedState_lookup_rhs (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "rhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "rhs" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "rhs" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "rhs" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_rhs s oracleVals

theorem skyReducerScalarsLoadedState_lookup_stack (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "stack" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "stack" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stack" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "stack" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_stack s oracleVals

theorem skyReducerScalarsLoadedState_lookup_oracleRefs (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "oracleRefs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "oracleRefs" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "oracleRefs" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "oracleRefs" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_oracleRefs s oracleVals

theorem skyReducerScalarsLoadedState_lookup_oracleValues (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).lookupVar "oracleValues" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).oracleValsBase)) := by
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "oracleValues" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "oracleValues" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "oracleValues" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_oracleValues s oracleVals

theorem skyReducerAppTagLoadedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "focus" =
      some (.int (Int.ofNat s.focus)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "focus"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "focus" ≠ "tag"))

theorem skyReducerAppTagLoadedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "stackSize"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "stackSize" ≠ "tag"))

theorem skyReducerAppTagLoadedState_lookup_stack
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stack" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "stack"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "stack" ≠ "tag"))

theorem skyReducerAppTagLoadedState_lookup_oracleRefs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "oracleRefs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "oracleRefs"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "oracleRefs" ≠ "tag"))

theorem skyReducerAppTagLoadedState_lookup_oracleValues
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "oracleValues" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).oracleValsBase)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "oracleValues"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "oracleValues" ≠ "tag"))

theorem skyReducerAppTagLoadedState_lookup_lhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "lhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "lhs"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "lhs" ≠ "tag"))

theorem skyReducerAppTagLoadedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "nodeCount"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "nodeCount" ≠ "tag"))

theorem skyReducerAppTagLoadedState_lookup_focusPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "focusPtr"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "focusPtr" ≠ "tag"))

theorem skyReducerAppTagLoadedState_lookup_stackSizePtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "stackSizePtr"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "stackSizePtr" ≠ "tag"))

theorem skyReducerAppTagLoadedState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  rw [skyReducerAppTagLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "nodeCountPtr"
      (.int (s.tags[s.focus]'hfocus)) (by decide : "nodeCountPtr" ≠ "tag"))

theorem execStmt_commitAndReturn_tagLoaded
    (code : StepStatus) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    execStmt 4 (SKYLowering.commitAndReturn code) (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int code.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
  exact execStmt_commitAndReturn_of_lookups code
    (skyReducerAppTagLoadedState s oracleVals hfocus)
    (layoutForState s oracleVals)
    (.int (Int.ofNat s.focus))
    (.int (Int.ofNat s.stack.length))
    (.int (Int.ofNat s.nodeCount))
    (skyReducerAppTagLoadedState_lookup_focusPtr s oracleVals hfocus)
    (skyReducerAppTagLoadedState_lookup_focus s oracleVals hfocus)
    (skyReducerAppTagLoadedState_lookup_stackSizePtr s oracleVals hfocus)
    (skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus)
    (skyReducerAppTagLoadedState_lookup_nodeCountPtr s oracleVals hfocus)
    (skyReducerAppTagLoadedState_lookup_nodeCount s oracleVals hfocus)

theorem skyReducerAppXLoadedState_lookup_x
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "x" =
      some (skyReducerAppXVal s hwf hfocus) := by
  rw [skyReducerAppXLoadedState]
  simpa using
    (lookupVar_updateVar_eq (skyReducerAppTagLoadedState s oracleVals hfocus)
      "x" (skyReducerAppXVal s hwf hfocus))

theorem skyReducerAppXLoadedState_lookup_stack
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "stack" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
  rw [skyReducerAppXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "stack"
      (skyReducerAppXVal s hwf hfocus) (by decide : "stack" ≠ "x"))

theorem skyReducerAppXLoadedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerAppXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "stackSize"
      (skyReducerAppXVal s hwf hfocus) (by decide : "stackSize" ≠ "x"))

theorem skyReducerAppXLoadedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "focus" =
      some (.int (Int.ofNat s.focus)) := by
  rw [skyReducerAppXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "focus"
      (skyReducerAppXVal s hwf hfocus) (by decide : "focus" ≠ "x"))

theorem skyReducerAppXLoadedState_lookup_lhs
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "lhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
  rw [skyReducerAppXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "lhs"
      (skyReducerAppXVal s hwf hfocus) (by decide : "lhs" ≠ "x"))

theorem skyReducerAppXLoadedState_lookup_focusPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  rw [skyReducerAppXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "focusPtr" (skyReducerAppXVal s hwf hfocus) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "focusPtr" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "focusPtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focusPtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "focusPtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_focusPtr s oracleVals

theorem skyReducerAppXLoadedState_lookup_stackSizePtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  rw [skyReducerAppXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "stackSizePtr" (skyReducerAppXVal s hwf hfocus) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "stackSizePtr" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "stackSizePtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stackSizePtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "stackSizePtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_stackSizePtr s oracleVals

theorem skyReducerAppXLoadedState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  rw [skyReducerAppXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "nodeCountPtr" (skyReducerAppXVal s hwf hfocus) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "nodeCountPtr" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "nodeCountPtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCountPtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCountPtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_nodeCountPtr s oracleVals

theorem skyReducerAppXLoadedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerAppXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "nodeCount" (skyReducerAppXVal s hwf hfocus) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "nodeCount" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  exact skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals

@[simp] theorem writeNatList_readInt_before (heap : Heap) (base addr : Nat) (xs : List Nat)
    (haddr : addr < base) :
    readIntCell? (writeNatList heap base xs) addr = readIntCell? heap addr := by
  induction xs generalizing heap base with
  | nil =>
      simp [writeNatList]
  | cons x xs ih =>
      have hlt : addr < base + 1 := Nat.lt.step haddr
      calc
        readIntCell? (writeNatList (heap.write base (.int (Int.ofNat x))) (base + 1) xs) addr =
            readIntCell? (heap.write base (.int (Int.ofNat x))) addr := by
              simpa [readIntCell?, Heap.read] using
                ih (heap := heap.write base (.int (Int.ofNat x))) (base := base + 1) hlt
        _ = readIntCell? heap addr := by
              simp [readIntCell?, Heap.read, Heap.write, Nat.ne_of_lt haddr]

theorem execStmt_loadFocus_skyReducerEntry (s : State) (oracleVals : Array Int) :
    execStmt 5 (.assign (.var "focus") (.deref (.var "focusPtr"))) (skyReducerEntry s oracleVals) =
      some (.normal ((skyReducerEntry s oracleVals).updateVar "focus" (.int (Int.ofNat s.focus)))) := by
  simp [execStmt, skyReducerEntry_eval_focusPtr]

theorem execStmt_loadStackSize_skyReducerFocusLoaded (s : State) (oracleVals : Array Int) :
    execStmt 5 (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
      (skyReducerFocusLoadedState s oracleVals) =
        some (.normal (skyReducerStackSizeLoadedState s oracleVals)) := by
  simp [execStmt, skyReducerFocusLoadedState_eval_stackSizePtr, skyReducerStackSizeLoadedState]

theorem execStmt_loadNodeCount_skyReducerStackSizeLoaded (s : State) (oracleVals : Array Int) :
    execStmt 5 (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
      (skyReducerStackSizeLoadedState s oracleVals) =
        some (.normal (skyReducerScalarsLoadedState s oracleVals)) := by
  simp [execStmt, skyReducerStackSizeLoadedState_eval_nodeCountPtr, skyReducerScalarsLoadedState]

theorem execStmt_loadScalars_skyReducerEntry (s : State) (oracleVals : Array Int) :
    execStmt 14
      (SKYLowering.seqs
        [ .assign (.var "focus") (.deref (.var "focusPtr"))
        , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
        , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr")) ])
      (skyReducerEntry s oracleVals) =
        some (.normal (skyReducerScalarsLoadedState s oracleVals)) := by
  calc
    execStmt 14
        (SKYLowering.seqs
          [ .assign (.var "focus") (.deref (.var "focusPtr"))
          , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
          , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr")) ])
        (skyReducerEntry s oracleVals)
      = execStmt 9
          (SKYLowering.seqs
            [ .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
            , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr")) ])
          (skyReducerFocusLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 9
              (.assign (.var "focus") (.deref (.var "focusPtr")))
              (SKYLowering.seqs
                [ .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
                , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr")) ])
              (skyReducerEntry s oracleVals)
              (skyReducerFocusLoadedState s oracleVals)
              (by simpa [SKYLowering.seqs, skyReducerFocusLoadedState] using
                execStmt_loadFocus_skyReducerEntry s oracleVals)
    _ = execStmt 4
          (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
          (skyReducerStackSizeLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 4
              (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (skyReducerFocusLoadedState s oracleVals)
              (skyReducerStackSizeLoadedState s oracleVals)
              (execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals)
    _ = some (.normal (skyReducerScalarsLoadedState s oracleVals)) := by
          simpa using execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals

theorem skyReducerScalarsLoadedState_eval_focusLtNodeCount (s : State) (oracleVals : Array Int) :
    evalExpr (.binop .lt (.var "focus") (.var "nodeCount")) (skyReducerScalarsLoadedState s oracleVals) =
      some (.int (if s.focus < s.nodeCount then 1 else 0)) := by
  simp [evalExpr, evalStaticExpr, skyReducerScalarsLoadedState_lookup_focus,
    skyReducerScalarsLoadedState_lookup_nodeCount]

theorem execStmt_guard_true_skyReducerScalarsLoaded
    (s : State) (oracleVals : Array Int) (th el : CStmt) (hfocus : s.focus < s.nodeCount) :
    execStmt 5 (.ite (.binop .lt (.var "focus") (.var "nodeCount")) th el)
      (skyReducerScalarsLoadedState s oracleVals) =
        execStmt 4 th (skyReducerScalarsLoadedState s oracleVals) := by
  rw [execStmt_ite_of_eval_true
    (fuel := 4) (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
    (th := th) (el := el) (st := skyReducerScalarsLoadedState s oracleVals)
    (v := .int (if s.focus < s.nodeCount then 1 else 0))]
  · exact skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals
  · simp [hfocus, isTruthy]

theorem execStmt_guard_false_skyReducerScalarsLoaded
    (s : State) (oracleVals : Array Int) (th el : CStmt) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt 5 (.ite (.binop .lt (.var "focus") (.var "nodeCount")) th el)
      (skyReducerScalarsLoadedState s oracleVals) =
        execStmt 4 el (skyReducerScalarsLoadedState s oracleVals) := by
  rw [execStmt_ite_of_eval_false
    (fuel := 4) (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
    (th := th) (el := el) (st := skyReducerScalarsLoadedState s oracleVals)
    (v := .int (if s.focus < s.nodeCount then 1 else 0))]
  · exact skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals
  · simp [hfocus, isTruthy]

theorem execStmt_guard_false_skyReducerScalarsLoaded_fuel
    (extra : Nat) (s : State) (oracleVals : Array Int) (th el : CStmt)
    (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt (5 + extra) (.ite (.binop .lt (.var "focus") (.var "nodeCount")) th el)
      (skyReducerScalarsLoadedState s oracleVals) =
        execStmt (4 + extra) el (skyReducerScalarsLoadedState s oracleVals) := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (execStmt_ite_of_eval_false
      (fuel := 4 + extra) (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
      (th := th) (el := el) (st := skyReducerScalarsLoadedState s oracleVals)
      (v := .int (if s.focus < s.nodeCount then 1 else 0))
      (skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals)
      (by simp [hfocus, isTruthy]))

theorem heap_write_eq_of_read_eq (heap : Heap) (addr : Nat) (v : CVal)
    (hread : heap.read addr = some v) :
    heap.write addr v = heap := by
  apply Finmap.ext_lookup
  intro addr'
  by_cases haddr : addr' = addr
  · subst haddr
    simpa [Heap.read, Heap.write] using hread.symm
  · simp [Heap.read, Heap.write, Finmap.lookup_insert_of_ne, haddr]

theorem heap_read_eq_of_readNatCell_eq (heap : Heap) (addr n : Nat)
    (hread : readNatCell? heap addr = some n) :
    heap.read addr = some (.int (Int.ofNat n)) := by
  unfold readNatCell? readIntCell? at hread
  cases hcell : heap.read addr <;> simp [hcell] at hread
  case some v =>
    cases v <;> simp [hcell] at hread
    case int m =>
      by_cases hnonneg : 0 ≤ m
      · simp [hnonneg] at hread
        have hm : m = Int.ofNat n := by
          calc
            m = Int.ofNat m.toNat := by simpa [hnonneg] using (Int.ofNat_of_nonneg hnonneg).symm
            _ = Int.ofNat n := by simpa using congrArg Int.ofNat hread
        simp [hcell, hm]
      · simp [hnonneg] at hread

theorem heap_write_eq_of_readNatCell_eq (heap : Heap) (addr n : Nat)
    (hread : readNatCell? heap addr = some n) :
    heap.write addr (.int (Int.ofNat n)) = heap := by
  exact heap_write_eq_of_read_eq heap addr (.int (Int.ofNat n))
    (heap_read_eq_of_readNatCell_eq heap addr n hread)

theorem skyReducerScalarsLoadedState_heap_eq_encodeHeapWithLayout
    (s : State) (oracleVals : Array Int) :
    (skyReducerScalarsLoadedState s oracleVals).heap =
      encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals := by
  simp [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, updateVar_heap,
    HeytingLean.LeanCP.enterBlockState_heap, encodeExecStateWithLayout]

def skyReducerUnchangedFocusCommitState (s : State) (oracleVals : Array Int) : CState :=
  (skyReducerScalarsLoadedState s oracleVals).withHeap
    ((skyReducerScalarsLoadedState s oracleVals).heap.write
      (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus)))

def skyReducerUnchangedStackSizeCommitState (s : State) (oracleVals : Array Int) : CState :=
  (skyReducerUnchangedFocusCommitState s oracleVals).withHeap
    ((skyReducerUnchangedFocusCommitState s oracleVals).heap.write
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length)))

def skyReducerUnchangedCommittedState (s : State) (oracleVals : Array Int) : CState :=
  (skyReducerUnchangedStackSizeCommitState s oracleVals).withHeap
    ((skyReducerUnchangedStackSizeCommitState s oracleVals).heap.write
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount)))

def skyReducerTagLoadedUnchangedFocusCommitState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerAppTagLoadedState s oracleVals hfocus).withHeap
    ((skyReducerAppTagLoadedState s oracleVals hfocus).heap.write
      (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus)))

def skyReducerTagLoadedUnchangedStackSizeCommitState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).withHeap
    ((skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap.write
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length)))

def skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) : CState :=
  (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).withHeap
    ((skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap.write
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount)))

theorem skyReducerUnchangedFocusCommitState_lookup_focusPtr
    (s : State) (oracleVals : Array Int) :
    (skyReducerUnchangedFocusCommitState s oracleVals).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  simpa [skyReducerUnchangedFocusCommitState] using
    skyReducerScalarsLoadedState_lookup_focusPtr s oracleVals

theorem skyReducerUnchangedFocusCommitState_lookup_stackSizePtr
    (s : State) (oracleVals : Array Int) :
    (skyReducerUnchangedFocusCommitState s oracleVals).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  simpa [skyReducerUnchangedFocusCommitState] using
    skyReducerScalarsLoadedState_lookup_stackSizePtr s oracleVals

theorem skyReducerUnchangedFocusCommitState_lookup_stackSize
    (s : State) (oracleVals : Array Int) :
    (skyReducerUnchangedFocusCommitState s oracleVals).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  simpa [skyReducerUnchangedFocusCommitState] using
    skyReducerScalarsLoadedState_lookup_stackSize s oracleVals

theorem skyReducerUnchangedFocusCommitState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) :
    (skyReducerUnchangedFocusCommitState s oracleVals).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  simpa [skyReducerUnchangedFocusCommitState] using
    skyReducerScalarsLoadedState_lookup_nodeCountPtr s oracleVals

theorem skyReducerUnchangedStackSizeCommitState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) :
    (skyReducerUnchangedStackSizeCommitState s oracleVals).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  simpa [skyReducerUnchangedStackSizeCommitState] using
    skyReducerUnchangedFocusCommitState_lookup_nodeCountPtr s oracleVals

theorem skyReducerUnchangedStackSizeCommitState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) :
    (skyReducerUnchangedStackSizeCommitState s oracleVals).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  simpa [skyReducerUnchangedStackSizeCommitState] using
    skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals

theorem execStmt_writeFocusPtr_skyReducerScalarsLoaded
    (s : State) (oracleVals : Array Int) :
    execStmt 2 (SKYLowering.writeScalar "focusPtr" (.var "focus"))
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.normal (skyReducerUnchangedFocusCommitState s oracleVals)) := by
  simpa [skyReducerUnchangedFocusCommitState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerScalarsLoadedState s oracleVals) "focusPtr" "focus"
      (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))
      (skyReducerScalarsLoadedState_lookup_focusPtr s oracleVals)
      (skyReducerScalarsLoadedState_lookup_focus s oracleVals))

theorem execStmt_writeStackSizePtr_skyReducerUnchangedFocusCommitState
    (s : State) (oracleVals : Array Int) :
    execStmt 2 (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
      (skyReducerUnchangedFocusCommitState s oracleVals) =
        some (.normal (skyReducerUnchangedStackSizeCommitState s oracleVals)) := by
  simpa [skyReducerUnchangedStackSizeCommitState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerUnchangedFocusCommitState s oracleVals) "stackSizePtr" "stackSize"
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))
      (skyReducerUnchangedFocusCommitState_lookup_stackSizePtr s oracleVals)
      (skyReducerUnchangedFocusCommitState_lookup_stackSize s oracleVals))

theorem execStmt_writeNodeCountPtr_skyReducerUnchangedStackSizeCommitState
    (s : State) (oracleVals : Array Int) :
    execStmt 2 (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
      (skyReducerUnchangedStackSizeCommitState s oracleVals) =
        some (.normal (skyReducerUnchangedCommittedState s oracleVals)) := by
  simpa [skyReducerUnchangedCommittedState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerUnchangedStackSizeCommitState s oracleVals) "nodeCountPtr" "nodeCount"
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))
      (skyReducerUnchangedStackSizeCommitState_lookup_nodeCountPtr s oracleVals)
      (skyReducerUnchangedStackSizeCommitState_lookup_nodeCount s oracleVals))

theorem execStmt_commitAndReturn_unchanged
    (code : StepStatus) (s : State) (oracleVals : Array Int) :
    execStmt 4 (SKYLowering.commitAndReturn code) (skyReducerScalarsLoadedState s oracleVals) =
      some (.returned (.int code.code) (skyReducerUnchangedCommittedState s oracleVals)) := by
  exact execStmt_commitAndReturn_of_steps code
    (st := skyReducerScalarsLoadedState s oracleVals)
    (stFocus := skyReducerUnchangedFocusCommitState s oracleVals)
    (stStack := skyReducerUnchangedStackSizeCommitState s oracleVals)
    (stDone := skyReducerUnchangedCommittedState s oracleVals)
    (execStmt_writeFocusPtr_skyReducerScalarsLoaded s oracleVals)
    (execStmt_writeStackSizePtr_skyReducerUnchangedFocusCommitState s oracleVals)
    (execStmt_writeNodeCountPtr_skyReducerUnchangedStackSizeCommitState s oracleVals)

theorem execStmt_commitAndReturn_unchanged_fuel
    (code : StepStatus) (extra : Nat) (s : State) (oracleVals : Array Int) :
    execStmt (4 + extra) (SKYLowering.commitAndReturn code) (skyReducerScalarsLoadedState s oracleVals) =
      some (.returned (.int code.code) (skyReducerUnchangedCommittedState s oracleVals)) := by
  exact execStmt_fuel_mono (h := execStmt_commitAndReturn_unchanged code s oracleVals)

theorem execStmt_guardFalse_skyReducerScalarsLoaded_halted
    (s : State) (oracleVals : Array Int) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt 5
      (.ite
        (.binop .lt (.var "focus") (.var "nodeCount"))
        (.seq
          (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted)))
        (SKYLowering.commitAndReturn .halted))
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (skyReducerUnchangedCommittedState s oracleVals)) := by
  rw [execStmt_guard_false_skyReducerScalarsLoaded
    (th := .seq
      (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted)))
    (el := SKYLowering.commitAndReturn .halted) (hfocus := hfocus)]
  simpa using execStmt_commitAndReturn_unchanged StepStatus.halted s oracleVals

theorem execStmt_focusOutOfRange_skyReducerEntry_unchangedCommitted
    (s : State) (oracleVals : Array Int) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt 19
      (SKYLowering.seqs
        [ .assign (.var "focus") (.deref (.var "focusPtr"))
        , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
        , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
        , .ite
            (.binop .lt (.var "focus") (.var "nodeCount"))
            (.seq
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted)))
            (SKYLowering.commitAndReturn .halted) ])
      (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (skyReducerUnchangedCommittedState s oracleVals)) := by
  let loadFocus : CStmt := .assign (.var "focus") (.deref (.var "focusPtr"))
  let loadStackSize : CStmt := .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
  let loadNodeCount : CStmt := .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
  let tagSwitch : CStmt :=
    switchMany (.var "tag")
      [ (NodeTag.code .app, SKYLowering.appCase)
      , (NodeTag.code .combK, SKYLowering.kCase)
      , (NodeTag.code .combS, SKYLowering.sCase)
      , (NodeTag.code .combY, SKYLowering.yCase)
      , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
      (SKYLowering.commitAndReturn .halted)
  let guard : CStmt :=
    .ite
      (.binop .lt (.var "focus") (.var "nodeCount"))
      (.seq (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus"))) tagSwitch)
      (SKYLowering.commitAndReturn .halted)
  change execStmt 19 (SKYLowering.seqs [loadFocus, loadStackSize, loadNodeCount, guard])
      (skyReducerEntry s oracleVals) =
    some (.returned (.int StepStatus.halted.code) (skyReducerUnchangedCommittedState s oracleVals))
  simp [SKYLowering.seqs]
  have hLoadFocus :
      execStmt 18 loadFocus (skyReducerEntry s oracleVals) =
        some (.normal (skyReducerFocusLoadedState s oracleVals)) := by
    simpa [loadFocus, skyReducerFocusLoadedState] using
      (execStmt_fuel_mono (extra := 13) (h := execStmt_loadFocus_skyReducerEntry s oracleVals))
  have hLoadStackSize :
      execStmt 17 loadStackSize (skyReducerFocusLoadedState s oracleVals) =
        some (.normal (skyReducerStackSizeLoadedState s oracleVals)) := by
    simpa [loadStackSize] using
      (execStmt_fuel_mono (extra := 12) (h := execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals))
  have hLoadNodeCount :
      execStmt 16 loadNodeCount (skyReducerStackSizeLoadedState s oracleVals) =
        some (.normal (skyReducerScalarsLoadedState s oracleVals)) := by
    simpa [loadNodeCount] using
      (execStmt_fuel_mono (extra := 11) (h := execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals))
  rw [execStmt_seq_of_normal 18 loadFocus (.seq loadStackSize (.seq loadNodeCount guard))
      (skyReducerEntry s oracleVals) (skyReducerFocusLoadedState s oracleVals) hLoadFocus]
  rw [execStmt_seq_of_normal 17 loadStackSize (.seq loadNodeCount guard)
      (skyReducerFocusLoadedState s oracleVals) (skyReducerStackSizeLoadedState s oracleVals) hLoadStackSize]
  rw [execStmt_seq_of_normal 16 loadNodeCount guard
      (skyReducerStackSizeLoadedState s oracleVals) (skyReducerScalarsLoadedState s oracleVals) hLoadNodeCount]
  simpa [guard, tagSwitch] using
    (execStmt_fuel_mono (extra := 11) (h := execStmt_guardFalse_skyReducerScalarsLoaded_halted s oracleVals hfocus))

theorem execStmt_writeFocusPtr_skyReducerAppTagLoadedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    execStmt 2 (SKYLowering.writeScalar "focusPtr" (.var "focus"))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.normal (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus)) := by
  simpa [skyReducerTagLoadedUnchangedFocusCommitState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerAppTagLoadedState s oracleVals hfocus) "focusPtr" "focus"
      (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))
      (skyReducerAppTagLoadedState_lookup_focusPtr s oracleVals hfocus)
      (skyReducerAppTagLoadedState_lookup_focus s oracleVals hfocus))

theorem execStmt_writeStackSizePtr_skyReducerTagLoadedUnchangedFocusCommitState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    execStmt 2 (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
      (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus) =
        some (.normal (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus)) := by
  simpa [skyReducerTagLoadedUnchangedStackSizeCommitState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus) "stackSizePtr" "stackSize"
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))
      (by
        rw [skyReducerTagLoadedUnchangedFocusCommitState]
        simpa using
          skyReducerAppTagLoadedState_lookup_stackSizePtr s oracleVals hfocus)
      (by
        rw [skyReducerTagLoadedUnchangedFocusCommitState]
        simpa using
          skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus))

theorem execStmt_writeNodeCountPtr_skyReducerTagLoadedUnchangedStackSizeCommitState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    execStmt 2 (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
      (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus) =
        some (.normal (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus)) := by
  simpa [skyReducerTagLoadedUnchangedCommittedState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus) "nodeCountPtr" "nodeCount"
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))
      (by
        rw [skyReducerTagLoadedUnchangedStackSizeCommitState]
        simpa using
          skyReducerAppTagLoadedState_lookup_nodeCountPtr s oracleVals hfocus)
      (by
        rw [skyReducerTagLoadedUnchangedStackSizeCommitState]
        simpa using
          skyReducerAppTagLoadedState_lookup_nodeCount s oracleVals hfocus))

theorem execStmt_commitAndReturn_tagLoadedUnchanged
    (code : StepStatus) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    execStmt 4 (SKYLowering.commitAndReturn code) (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int code.code) (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus)) := by
  exact execStmt_commitAndReturn_of_steps code
    (st := skyReducerAppTagLoadedState s oracleVals hfocus)
    (stFocus := skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus)
    (stStack := skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus)
    (stDone := skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus)
    (execStmt_writeFocusPtr_skyReducerAppTagLoadedState s oracleVals hfocus)
    (execStmt_writeStackSizePtr_skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus)
    (execStmt_writeNodeCountPtr_skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus)

theorem execStmt_commitAndReturn_tagLoadedUnchanged_fuel
    (code : StepStatus) (extra : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    execStmt (4 + extra) (SKYLowering.commitAndReturn code) (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int code.code) (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus)) := by
  exact execStmt_fuel_mono (h := execStmt_commitAndReturn_tagLoadedUnchanged code s oracleVals hfocus)

theorem decodeKernelState?_heap_eq
    (maxNodes : Nat) (layout : ExecLayout) (st₁ st₂ : CState)
    (hHeap : st₁.heap = st₂.heap) :
    decodeKernelState? maxNodes layout st₁ = decodeKernelState? maxNodes layout st₂ := by
  simp [decodeKernelState?, hHeap]

@[simp] theorem readIntCell?_write_same (heap : Heap) (addr : Nat) (n : Int) :
    readIntCell? (heap.write addr (.int n)) addr = some n := by
  simp [readIntCell?, Heap.read, Heap.write]

@[simp] theorem readNatCell?_write_same (heap : Heap) (addr n : Nat) :
    readNatCell? (heap.write addr (.int (Int.ofNat n))) addr = some n := by
  simp [readNatCell?, readIntCell?, Heap.read, Heap.write]

@[simp] theorem readIntCell?_write_other (heap : Heap) (readAddr writeAddr : Nat) (v : CVal)
    (hneq : readAddr ≠ writeAddr) :
    readIntCell? (heap.write writeAddr v) readAddr = readIntCell? heap readAddr := by
  simp [readIntCell?, Heap.read, Heap.write, hneq]

@[simp] theorem readNatCell?_write_other (heap : Heap) (readAddr writeAddr : Nat) (v : CVal)
    (hneq : readAddr ≠ writeAddr) :
    readNatCell? (heap.write writeAddr v) readAddr = readNatCell? heap readAddr := by
  simp [readNatCell?, readIntCell?, Heap.read, Heap.write, hneq]

@[simp] theorem writeIntList_read_before (heap : Heap) (base addr : Nat) (xs : List Int)
    (haddr : addr < base) :
    readIntCell? (writeIntList heap base xs) addr = readIntCell? heap addr := by
  induction xs generalizing heap base with
  | nil =>
      simp [writeIntList]
  | cons x xs ih =>
      have hlt : addr < base + 1 := Nat.lt.step haddr
      calc
        readIntCell? (writeIntList (heap.write base (.int x)) (base + 1) xs) addr =
            readIntCell? (heap.write base (.int x)) addr := by
              simpa [readIntCell?, Heap.read] using ih (heap := heap.write base (.int x)) (base := base + 1) hlt
        _ = readIntCell? heap addr := by
              simp [readIntCell?, Heap.read, Heap.write, Nat.ne_of_lt haddr]

@[simp] theorem writeNatList_read_before (heap : Heap) (base addr : Nat) (xs : List Nat)
    (haddr : addr < base) :
    readNatCell? (writeNatList heap base xs) addr = readNatCell? heap addr := by
  induction xs generalizing heap base with
  | nil =>
      simp [writeNatList]
  | cons x xs ih =>
      have hlt : addr < base + 1 := Nat.lt.step haddr
      calc
        readNatCell? (writeNatList (heap.write base (.int (Int.ofNat x))) (base + 1) xs) addr =
            readNatCell? (heap.write base (.int (Int.ofNat x))) addr := by
              simpa [readNatCell?, readIntCell?, Heap.read] using
                ih (heap := heap.write base (.int (Int.ofNat x))) (base := base + 1) hlt
        _ = readNatCell? heap addr := by
              simp [readNatCell?, readIntCell?, Heap.read, Heap.write, Nat.ne_of_lt haddr]

@[simp] theorem writeIntList_readNat_before (heap : Heap) (base addr : Nat) (xs : List Int)
    (haddr : addr < base) :
    readNatCell? (writeIntList heap base xs) addr = readNatCell? heap addr := by
  induction xs generalizing heap base with
  | nil =>
      simp [writeIntList]
  | cons x xs ih =>
      have hlt : addr < base + 1 := Nat.lt.step haddr
      calc
        readNatCell? (writeIntList (heap.write base (.int x)) (base + 1) xs) addr =
            readNatCell? (heap.write base (.int x)) addr := by
              simpa [readNatCell?, readIntCell?, Heap.read] using
                ih (heap := heap.write base (.int x)) (base := base + 1) hlt
        _ = readNatCell? heap addr := by
              simp [readNatCell?, readIntCell?, Heap.read, Heap.write, Nat.ne_of_lt haddr]

@[simp] theorem readIntList?_writeIntList (heap : Heap) (base : Nat) (xs : List Int) :
    readIntList? (writeIntList heap base xs) base xs.length = some xs := by
  induction xs generalizing heap base with
  | nil =>
      simp [readIntList?, writeIntList]
  | cons x xs ih =>
      have hread :
          readIntCell? (writeIntList (heap.write base (.int x)) (base + 1) xs) base = some x := by
        calc
          readIntCell? (writeIntList (heap.write base (.int x)) (base + 1) xs) base =
              readIntCell? (heap.write base (.int x)) base := by
                simpa using
                  (writeIntList_read_before (heap := heap.write base (.int x))
                    (base := base + 1) (addr := base) xs (Nat.lt_succ_self base))
          _ = some x := by
                simp [readIntCell?, Heap.read, Heap.write]
      simp [readIntList?, writeIntList, hread, ih]

@[simp] theorem readNatList?_writeNatList (heap : Heap) (base : Nat) (xs : List Nat) :
    readNatList? (writeNatList heap base xs) base xs.length = some xs := by
  induction xs generalizing heap base with
  | nil =>
      simp [readNatList?, writeNatList]
  | cons x xs ih =>
      have hhead : readNatCell? (heap.write base (.int (Int.ofNat x))) base = some x := by
        simp [readNatCell?, readIntCell?, Heap.read, Heap.write]
      have htail :
          readNatList? (writeNatList (heap.write base (.int (Int.ofNat x))) (base + 1) xs)
            (base + 1) xs.length = some xs := by
        simpa using ih (heap := heap.write base (.int (Int.ofNat x))) (base := base + 1)
      have hhead' : readNatCell? (heap.write base (.int (↑x : Int))) base = some x := by
        simpa using hhead
      have htail' :
          readNatList? (writeNatList (heap.write base (.int (↑x : Int))) (base + 1) xs)
            (base + 1) xs.length = some xs := by
        simpa using htail
      simp [readNatList?, writeNatList]
      rw [hhead', htail']
      simp

theorem readIntList?_write_other (heap : Heap) (writeAddr : Nat) (v : CVal)
    (base count : Nat) (hdisj : writeAddr < base ∨ base + count ≤ writeAddr) :
    readIntList? (heap.write writeAddr v) base count = readIntList? heap base count := by
  induction count generalizing base with
  | zero =>
      simp [readIntList?]
  | succ count ih =>
      have hneq : writeAddr ≠ base := by
        cases hdisj with
        | inl hlt => exact Nat.ne_of_lt hlt
        | inr hge =>
            have hlt : base < writeAddr := by
              omega
            exact Nat.ne_of_gt hlt
      have htail : writeAddr < base + 1 ∨ (base + 1) + count ≤ writeAddr := by
        cases hdisj with
        | inl hlt => exact Or.inl (Nat.lt.step hlt)
        | inr hge => exact Or.inr (by omega)
      rw [readIntList?]
      rw [readIntCell?_write_other heap base writeAddr v hneq.symm]
      rw [ih (base + 1) htail]
      simp [readIntList?]

theorem readNatList?_write_other (heap : Heap) (writeAddr : Nat) (v : CVal)
    (base count : Nat) (hdisj : writeAddr < base ∨ base + count ≤ writeAddr) :
    readNatList? (heap.write writeAddr v) base count = readNatList? heap base count := by
  induction count generalizing base with
  | zero =>
      simp [readNatList?]
  | succ count ih =>
      have hneq : writeAddr ≠ base := by
        cases hdisj with
        | inl hlt => exact Nat.ne_of_lt hlt
        | inr hge =>
            have hlt : base < writeAddr := by
              omega
            exact Nat.ne_of_gt hlt
      have htail : writeAddr < base + 1 ∨ (base + 1) + count ≤ writeAddr := by
        cases hdisj with
        | inl hlt => exact Or.inl (Nat.lt.step hlt)
        | inr hge => exact Or.inr (by omega)
      rw [readNatList?]
      rw [readNatCell?_write_other heap base writeAddr v hneq.symm]
      rw [ih (base + 1) htail]
      simp [readNatList?]

theorem readIntList?_writeIntList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Int)
    (base count : Nat) (hdisj : base + count ≤ writeBase) :
    readIntList? (writeIntList heap writeBase xs) base count = readIntList? heap base count := by
  induction xs generalizing heap writeBase with
  | nil =>
      simp [writeIntList]
  | cons x xs ih =>
      rw [writeIntList]
      rw [ih (heap := heap.write writeBase (.int x)) (writeBase := writeBase + 1) (hdisj := by omega)]
      exact readIntList?_write_other heap writeBase (.int x) base count (Or.inr hdisj)

theorem readIntList?_writeNatList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Nat)
    (base count : Nat) (hdisj : base + count ≤ writeBase) :
    readIntList? (writeNatList heap writeBase xs) base count = readIntList? heap base count := by
  induction xs generalizing heap writeBase with
  | nil =>
      simp [writeNatList]
  | cons x xs ih =>
      rw [writeNatList]
      rw [ih (heap := heap.write writeBase (.int (Int.ofNat x))) (writeBase := writeBase + 1)
        (hdisj := by omega)]
      exact readIntList?_write_other heap writeBase (.int (Int.ofNat x)) base count (Or.inr hdisj)

theorem readNatList?_writeIntList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Int)
    (base count : Nat) (hdisj : base + count ≤ writeBase) :
    readNatList? (writeIntList heap writeBase xs) base count = readNatList? heap base count := by
  induction xs generalizing heap writeBase with
  | nil =>
      simp [writeIntList]
  | cons x xs ih =>
      rw [writeIntList]
      rw [ih (heap := heap.write writeBase (.int x)) (writeBase := writeBase + 1) (hdisj := by omega)]
      exact readNatList?_write_other heap writeBase (.int x) base count (Or.inr hdisj)

theorem readNatList?_writeNatList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Nat)
    (base count : Nat) (hdisj : base + count ≤ writeBase) :
    readNatList? (writeNatList heap writeBase xs) base count = readNatList? heap base count := by
  induction xs generalizing heap writeBase with
  | nil =>
      simp [writeNatList]
  | cons x xs ih =>
      rw [writeNatList]
      rw [ih (heap := heap.write writeBase (.int (Int.ofNat x))) (writeBase := writeBase + 1)
        (hdisj := by omega)]
      exact readNatList?_write_other heap writeBase (.int (Int.ofNat x)) base count (Or.inr hdisj)

theorem readIntCell?_writeIntList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Int)
    (addr : Nat) (hdisj : writeBase + xs.length ≤ addr) :
    readIntCell? (writeIntList heap writeBase xs) addr = readIntCell? heap addr := by
  induction xs generalizing heap writeBase with
  | nil =>
      simp [writeIntList]
  | cons x xs ih =>
      have htail : writeBase + 1 + xs.length ≤ addr := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdisj
      have hneq : addr ≠ writeBase := by
        have hlt : writeBase < addr := by
          omega
        exact Nat.ne_of_gt hlt
      rw [writeIntList]
      rw [ih (heap := heap.write writeBase (.int x)) (writeBase := writeBase + 1) htail]
      exact readIntCell?_write_other heap addr writeBase (.int x) hneq

theorem readIntCell?_writeNatList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Nat)
    (addr : Nat) (hdisj : writeBase + xs.length ≤ addr) :
    readIntCell? (writeNatList heap writeBase xs) addr = readIntCell? heap addr := by
  induction xs generalizing heap writeBase with
  | nil =>
      simp [writeNatList]
  | cons x xs ih =>
      have htail : writeBase + 1 + xs.length ≤ addr := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdisj
      have hneq : addr ≠ writeBase := by
        have hlt : writeBase < addr := by
          omega
        exact Nat.ne_of_gt hlt
      rw [writeNatList]
      rw [ih (heap := heap.write writeBase (.int (Int.ofNat x))) (writeBase := writeBase + 1) htail]
      exact readIntCell?_write_other heap addr writeBase (.int (Int.ofNat x)) hneq

theorem readNatCell?_writeIntList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Int)
    (addr : Nat) (hdisj : writeBase + xs.length ≤ addr) :
    readNatCell? (writeIntList heap writeBase xs) addr = readNatCell? heap addr := by
  induction xs generalizing heap writeBase with
  | nil =>
      simp [writeIntList]
  | cons x xs ih =>
      have htail : writeBase + 1 + xs.length ≤ addr := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdisj
      have hneq : addr ≠ writeBase := by
        have hlt : writeBase < addr := by
          omega
        exact Nat.ne_of_gt hlt
      rw [writeIntList]
      rw [ih (heap := heap.write writeBase (.int x)) (writeBase := writeBase + 1) htail]
      exact readNatCell?_write_other heap addr writeBase (.int x) hneq

theorem readNatCell?_writeNatList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Nat)
    (addr : Nat) (hdisj : writeBase + xs.length ≤ addr) :
    readNatCell? (writeNatList heap writeBase xs) addr = readNatCell? heap addr := by
  induction xs generalizing heap writeBase with
  | nil =>
      simp [writeNatList]
  | cons x xs ih =>
      have htail : writeBase + 1 + xs.length ≤ addr := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdisj
      have hneq : addr ≠ writeBase := by
        have hlt : writeBase < addr := by
          omega
        exact Nat.ne_of_gt hlt
      rw [writeNatList]
      rw [ih (heap := heap.write writeBase (.int (Int.ofNat x))) (writeBase := writeBase + 1) htail]
      exact readNatCell?_write_other heap addr writeBase (.int (Int.ofNat x)) hneq

theorem readIntCell?_writeIntList_at (heap : Heap) (base : Nat) (xs : List Int)
    (i : Nat) (hi : i < xs.length) :
    readIntCell? (writeIntList heap base xs) (base + i) = some (xs.get ⟨i, hi⟩) := by
  induction xs generalizing heap base i with
  | nil =>
      cases hi
  | cons x xs ih =>
      cases i with
      | zero =>
          calc
            readIntCell? (writeIntList heap base (x :: xs)) (base + 0)
                = readIntCell? (writeIntList (heap.write base (.int x)) (base + 1) xs) base := by
                    simp [writeIntList]
            _ = readIntCell? (heap.write base (.int x)) base := by
                  simpa using
                    (writeIntList_read_before (heap := heap.write base (.int x))
                      (base := base + 1) (addr := base) xs (Nat.lt_succ_self base))
            _ = some x := by
                  simp [readIntCell?, Heap.read, Heap.write]
            _ = some ((x :: xs).get ⟨0, hi⟩) := by
                  simp
      | succ i =>
          have hi' : i < xs.length := by
            simpa using hi
          calc
            readIntCell? (writeIntList heap base (x :: xs)) (base + (i + 1))
                = readIntCell? (writeIntList (heap.write base (.int x)) (base + 1) xs) ((base + 1) + i) := by
                    simp [writeIntList, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = some (xs.get ⟨i, hi'⟩) := by
                  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                    ih (heap := heap.write base (.int x)) (base := base + 1) (i := i) hi'
            _ = some ((x :: xs).get ⟨i + 1, hi⟩) := by
                  simp

theorem readNatCell?_writeNatList_at (heap : Heap) (base : Nat) (xs : List Nat)
    (i : Nat) (hi : i < xs.length) :
    readNatCell? (writeNatList heap base xs) (base + i) = some (xs.get ⟨i, hi⟩) := by
  induction xs generalizing heap base i with
  | nil =>
      cases hi
  | cons x xs ih =>
      cases i with
      | zero =>
          calc
            readNatCell? (writeNatList heap base (x :: xs)) (base + 0)
                = readNatCell? (writeNatList (heap.write base (.int (Int.ofNat x))) (base + 1) xs) base := by
                    simp [writeNatList]
            _ = readNatCell? (heap.write base (.int (Int.ofNat x))) base := by
                  simpa using
                    (writeNatList_read_before (heap := heap.write base (.int (Int.ofNat x)))
                      (base := base + 1) (addr := base) xs (Nat.lt_succ_self base))
            _ = some x := by
                  simp [readNatCell?, readIntCell?, Heap.read, Heap.write]
            _ = some ((x :: xs).get ⟨0, hi⟩) := by
                  simp
      | succ i =>
          have hi' : i < xs.length := by
            simpa using hi
          calc
            readNatCell? (writeNatList heap base (x :: xs)) (base + (i + 1))
                = readNatCell? (writeNatList (heap.write base (.int (Int.ofNat x))) (base + 1) xs)
                    ((base + 1) + i) := by
                      simp [writeNatList, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = some (xs.get ⟨i, hi'⟩) := by
                  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                    ih (heap := heap.write base (.int (Int.ofNat x))) (base := base + 1) (i := i) hi'
            _ = some ((x :: xs).get ⟨i + 1, hi⟩) := by
                  simp

theorem skyReducerScalarsLoadedState_eval_tagAtFocus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    evalExpr (SKYLowering.loadAt "tags" (.var "focus")) (skyReducerScalarsLoadedState s oracleVals) =
      some (.int s.tags[s.focus]) := by
  rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, _hstack⟩
  have hfocusMax : s.focus < s.maxNodes := Nat.lt_of_lt_of_le hfocus hnodes
  have hload :
      evalExpr (SKYLowering.loadAt "tags" (.var "focus")) (skyReducerScalarsLoadedState s oracleVals) =
        (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).tagsBase + s.focus) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).tagsBase : Int) + ↑s.focus := by
      omega
    simpa [layoutForState, layoutFor, SKYLowering.loadAt, evalExpr, evalStaticExpr,
      skyReducerScalarsLoadedState_lookup_tags, skyReducerScalarsLoadedState_lookup_focus,
      CState.readPtr, CState.resolvePtr, CState.readCell,
      evalBinOp_add_int_int, evalBinOp_add_ptr_int, evalBinOp_add_int_ptr,
      HeytingLean.LeanCP.Addr.addOffset, HeytingLean.LeanCP.CVal.ptrAddr, hnonneg]
  have hcell :
      readIntCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals) s.focus =
        some s.tags[s.focus] := by
    simp only [encodeHeapWithLayout, encodeStackWithLayout, encodeOracleValuesWithLayout,
      encodeNodeArraysWithLayout, layoutForState, layoutFor, State.nodeCount] at *
    simp only [Nat.zero_add] at *
    have hfocusNeNodeCountBase :
        s.focus ≠
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
            (s.stack.length + 1) + 1 + 1 := by
      omega
    rw [readIntCell?_write_other _ _ _ _ hfocusNeNodeCountBase]
    have hfocusNeStackSizeBase :
        s.focus ≠
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
            (s.stack.length + 1) + 1 := by
      omega
    rw [readIntCell?_write_other _ _ _ _ hfocusNeStackSizeBase]
    have hfocusNeFocusBase :
        s.focus ≠
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
            (s.stack.length + 1) := by
      omega
    rw [readIntCell?_write_other _ _ _ _ hfocusNeFocusBase]
    have hstackBefore :
        s.focus < s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals := by
      omega
    rw [writeNatList_readInt_before _ _ _ _ hstackBefore]
    have horacleBefore : s.focus < s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes := by
      omega
    rw [writeIntList_read_before _ _ _ _ horacleBefore]
    have hrefsBefore : s.focus < s.maxNodes + s.maxNodes + s.maxNodes := by
      omega
    rw [writeNatList_readInt_before _ _ _ _ hrefsBefore]
    have hrhsBefore : s.focus < s.maxNodes + s.maxNodes := by
      omega
    rw [writeNatList_readInt_before _ _ _ _ hrhsBefore]
    have hlhsBefore : s.focus < s.maxNodes := hfocusMax
    rw [writeNatList_readInt_before _ _ _ _ hlhsBefore]
    simpa using
      (readIntCell?_writeIntList_at
        (heap := Heap.empty) (base := 0) (xs := s.tags.toList) (i := s.focus) hfocus)
  have hheap :
      (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).tagsBase + s.focus) =
        some (.int s.tags[s.focus]) := by
    have hheapEnc :
        (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read s.focus =
          some (.int s.tags[s.focus]) := by
      cases hread : (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read s.focus with
      | none =>
          simp [readIntCell?, hread] at hcell
      | some v =>
          cases v with
          | int n =>
              simp [readIntCell?, hread] at hcell
              simp [hread, hcell]
          | ptr block offset =>
              simp [readIntCell?, hread] at hcell
          | uint n sz =>
              simp [readIntCell?, hread] at hcell
          | float v =>
              simp [readIntCell?, hread] at hcell
          | null =>
              simp [readIntCell?, hread] at hcell
          | undef =>
              simp [readIntCell?, hread] at hcell
          | structVal fields =>
              simp [readIntCell?, hread] at hcell
          | unionVal tag v =>
              simp [readIntCell?, hread] at hcell
    simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
      skyReducerEntry, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
      encodeExecStateWithLayout, layoutForState, layoutFor] using hheapEnc
  rw [hload, hheap]

theorem skyReducerScalarsLoadedState_eval_lhsAtFocus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    evalExpr (SKYLowering.loadAt "lhs" (.var "focus")) (skyReducerScalarsLoadedState s oracleVals) =
      some (.int (Int.ofNat (s.lhs[s.focus]'(by
        rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
        simpa [hlhs] using hfocus)))) := by
  rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, _hstack⟩
  have hfocusMax : s.focus < s.maxNodes := Nat.lt_of_lt_of_le hfocus hnodes
  have hLhsPtr := skyReducerScalarsLoadedState_lookup_lhs s oracleVals
  have hFocusVar := skyReducerScalarsLoadedState_lookup_focus s oracleVals
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase))
        (.int (Int.ofNat s.focus)) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).lhsBase : Int) + ↑s.focus := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).lhsBase : Int) + ↑s.focus then
        some (CVal.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase + Int.ofNat s.focus))
      else none) = some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus)))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerScalarsLoadedState s oracleVals).readPtr
        { block := 0, offset := Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus) } =
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simpa using
      (CState.readPtr_block0 (skyReducerScalarsLoadedState s oracleVals)
        ((layoutForState s oracleVals).lhsBase + s.focus)
        ((layoutForState s oracleVals).lhsBase + s.focus))
  have hload :
      evalExpr (SKYLowering.loadAt "lhs" (.var "focus")) (skyReducerScalarsLoadedState s oracleVals) =
        (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hLhsPtr, hFocusVar, hAdd] using hReadPtr
  have hcell :
      readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals) (s.maxNodes + s.focus) =
        some (s.lhs[s.focus]'(by simpa [hlhs] using hfocus)) := by
    let h0 := writeIntList Heap.empty 0 s.tags.toList
    let h1 := writeNatList h0 s.maxNodes s.lhs.toList
    let h2 := writeNatList h1 (s.maxNodes + s.maxNodes) s.rhs.toList
    let h3 := writeNatList h2 (s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList
    let h4 := writeIntList h3 (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes)
      (oracleValuesPadded s oracleVals)
    let h5 := writeNatList h4
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals) s.stack.reverse
    let h6 := h5.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
      (.int (Int.ofNat s.focus))
    let h7 := h6.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
      (.int (Int.ofNat s.stack.length))
    let h8 := h7.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1)
      (.int (Int.ofNat s.nodeCount))
    have hcell' :
        readNatCell? h8 (s.maxNodes + s.focus) =
          some (s.lhs[s.focus]'(by simpa [hlhs] using hfocus)) := by
      simp only [h8, h7, h6]
      have hlhsAddrNeNodeCountBase :
          s.maxNodes + s.focus ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ hlhsAddrNeNodeCountBase]
      have hlhsAddrNeStackSizeBase :
          s.maxNodes + s.focus ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ hlhsAddrNeStackSizeBase]
      have hlhsAddrNeFocusBase :
          s.maxNodes + s.focus ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) := by
        omega
      rw [readNatCell?_write_other _ _ _ _ hlhsAddrNeFocusBase]
      have hstackBefore :
          s.maxNodes + s.focus <
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals := by
        omega
      rw [writeNatList_read_before _ _ _ _ hstackBefore]
      have horacleBefore : s.maxNodes + s.focus < s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes := by
        omega
      rw [writeIntList_readNat_before _ _ _ _ horacleBefore]
      have hrefsBefore : s.maxNodes + s.focus < s.maxNodes + s.maxNodes + s.maxNodes := by
        omega
      rw [writeNatList_read_before _ _ _ _ hrefsBefore]
      have hrhsBefore : s.maxNodes + s.focus < s.maxNodes + s.maxNodes := by
        omega
      rw [writeNatList_read_before _ _ _ _ hrhsBefore]
      simpa [h1, h0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (readNatCell?_writeNatList_at
          (heap := h0) (base := s.maxNodes) (xs := s.lhs.toList)
          (i := s.focus) (by simpa [hlhs] using hfocus))
    simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, encodeHeapWithLayout, encodeStackWithLayout,
      encodeOracleValuesWithLayout, encodeNodeArraysWithLayout, layoutForState, layoutFor, State.nodeCount]
      using hcell'
  have hheap :
      (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).lhsBase + s.focus) =
        some (.int (Int.ofNat (s.lhs[s.focus]'(by simpa [hlhs] using hfocus)))) := by
    have hheapEnc :
        (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read (s.maxNodes + s.focus) =
          some (.int (Int.ofNat (s.lhs[s.focus]'(by simpa [hlhs] using hfocus)))) := by
      cases hread : (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read (s.maxNodes + s.focus) with
      | none =>
          simp [readNatCell?, readIntCell?, hread] at hcell
      | some v =>
          cases v with
          | int n =>
              simp [readNatCell?, readIntCell?, hread] at hcell
              have hn :
                  n = Int.ofNat (s.lhs[s.focus]'(by simpa [hlhs] using hfocus)) := by
                calc
                  n = Int.ofNat n.toNat := by
                    symm
                    exact Int.toNat_of_nonneg hcell.1
                  _ = Int.ofNat (s.lhs[s.focus]'(by simpa [hlhs] using hfocus)) := by
                    simp [hcell.2]
              simp [hread, hn]
          | ptr block offset =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | uint n sz =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | float v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | null =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | undef =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | structVal fields =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | unionVal tag v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
    simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
      skyReducerEntry, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
      encodeExecStateWithLayout, layoutForState, layoutFor] using hheapEnc
  rw [hload, hheap]

theorem skyReducerScalarsLoadedState_heap_read_lhsAtFocus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    (skyReducerScalarsLoadedState s oracleVals).heap.read
      ((layoutForState s oracleVals).lhsBase + s.focus) =
        some (.int (Int.ofNat (s.lhs[s.focus]'(by
          rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
          simpa [hlhs] using hfocus)))) := by
  have hLhsLookup := skyReducerScalarsLoadedState_lookup_lhs s oracleVals
  have hFocusLookup := skyReducerScalarsLoadedState_lookup_focus s oracleVals
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase))
        (.int (Int.ofNat s.focus)) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).lhsBase : Int) + ↑s.focus := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).lhsBase : Int) + ↑s.focus then
        some (CVal.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase + Int.ofNat s.focus))
      else none) =
        some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus)))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerScalarsLoadedState s oracleVals).readPtr
        { block := 0, offset := Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus) } =
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simpa using
      (CState.readPtr_block0 (skyReducerScalarsLoadedState s oracleVals)
        ((layoutForState s oracleVals).lhsBase + s.focus)
        ((layoutForState s oracleVals).lhsBase + s.focus))
  have hload :
      evalExpr (SKYLowering.loadAt "lhs" (.var "focus")) (skyReducerScalarsLoadedState s oracleVals) =
        (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hLhsLookup, hFocusLookup, hAdd] using hReadPtr
  rw [← hload]
  exact skyReducerScalarsLoadedState_eval_lhsAtFocus s oracleVals hwf hfocus

theorem skyReducerAppStoredState_lookup_focus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStoredState s oracleVals hwf hfocus).lookupVar "focus" =
      some (.int (Int.ofNat s.focus)) := by
  simpa [skyReducerAppStoredState] using
    (skyReducerAppXLoadedState_lookup_focus s oracleVals hwf hfocus)

theorem skyReducerAppStoredState_lookup_lhs
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStoredState s oracleVals hwf hfocus).lookupVar "lhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
  simpa [skyReducerAppStoredState] using
    (skyReducerAppXLoadedState_lookup_lhs s oracleVals hwf hfocus)

theorem skyReducerAppXLoadedState_eval_lhsAtFocus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    evalExpr (SKYLowering.loadAt "lhs" (.var "focus")) (skyReducerAppXLoadedState s oracleVals hwf hfocus) =
      some (.int (Int.ofNat (s.lhs[s.focus]'(by
        rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
        simpa [hlhs] using hfocus)))) := by
  have hLhsLookup := skyReducerAppXLoadedState_lookup_lhs s oracleVals hwf hfocus
  have hFocusLookup := skyReducerAppXLoadedState_lookup_focus s oracleVals hwf hfocus
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase))
        (.int (Int.ofNat s.focus)) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).lhsBase : Int) + ↑s.focus := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).lhsBase : Int) + ↑s.focus then
        some (CVal.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase + Int.ofNat s.focus))
      else none) =
        some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus)))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerAppXLoadedState s oracleVals hwf hfocus).readPtr
        { block := 0, offset := Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus) } =
      (skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.read
        ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simpa using
      (CState.readPtr_block0 (skyReducerAppXLoadedState s oracleVals hwf hfocus)
        ((layoutForState s oracleVals).lhsBase + s.focus)
        ((layoutForState s oracleVals).lhsBase + s.focus))
  have hload :
      evalExpr (SKYLowering.loadAt "lhs" (.var "focus"))
          (skyReducerAppXLoadedState s oracleVals hwf hfocus) =
        (skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.read
          ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hLhsLookup, hFocusLookup, hAdd] using hReadPtr
  have hHeapSame :
      (skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.read
        ((layoutForState s oracleVals).lhsBase + s.focus) =
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simp [skyReducerAppXLoadedState, skyReducerAppTagLoadedState, updateVar_heap]
  rw [hload, hHeapSame]
  exact skyReducerScalarsLoadedState_heap_read_lhsAtFocus s oracleVals hwf hfocus

theorem skyReducerAppStoredState_eval_lhsAtFocus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    evalExpr (SKYLowering.loadAt "lhs" (.var "focus")) (skyReducerAppStoredState s oracleVals hwf hfocus) =
      some (.int (Int.ofNat (s.lhs[s.focus]'(by
        rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
        simpa [hlhs] using hfocus)))) := by
  have hLhsLookup := skyReducerAppStoredState_lookup_lhs s oracleVals hwf hfocus
  have hFocusLookup := skyReducerAppStoredState_lookup_focus s oracleVals hwf hfocus
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase))
        (.int (Int.ofNat s.focus)) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).lhsBase : Int) + ↑s.focus := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).lhsBase : Int) + ↑s.focus then
        some (CVal.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase + Int.ofNat s.focus))
      else none) =
        some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus)))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerAppStoredState s oracleVals hwf hfocus).readPtr
        { block := 0, offset := Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus) } =
      (skyReducerAppStoredState s oracleVals hwf hfocus).heap.read
        ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simpa using
      (CState.readPtr_block0 (skyReducerAppStoredState s oracleVals hwf hfocus)
        ((layoutForState s oracleVals).lhsBase + s.focus)
        ((layoutForState s oracleVals).lhsBase + s.focus))
  have hload :
      evalExpr (SKYLowering.loadAt "lhs" (.var "focus"))
          (skyReducerAppStoredState s oracleVals hwf hfocus) =
        (skyReducerAppStoredState s oracleVals hwf hfocus).heap.read
          ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hLhsLookup, hFocusLookup, hAdd] using hReadPtr
  have hAddrNe :
      (layoutForState s oracleVals).lhsBase + s.focus ≠
        (layoutForState s oracleVals).stackBase + s.stack.length := by
    rcases hwf with ⟨hlhs, _hrhs, _hrefs, hnodes, _hstack⟩
    simp [layoutForState, layoutFor]
    omega
  have hReadOther :
      (skyReducerAppStoredState s oracleVals hwf hfocus).heap.read
        ((layoutForState s oracleVals).lhsBase + s.focus) =
      (skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.read
        ((layoutForState s oracleVals).lhsBase + s.focus) := by
    simpa [skyReducerAppStoredState] using
      (heap_read_write_ne
        ((skyReducerAppXLoadedState s oracleVals hwf hfocus).heap)
        ((layoutForState s oracleVals).stackBase + s.stack.length)
        ((layoutForState s oracleVals).lhsBase + s.focus)
        (skyReducerAppXVal s hwf hfocus)
        hAddrNe)
  have hReadX :
      (skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.read
        ((layoutForState s oracleVals).lhsBase + s.focus) =
      some (.int (Int.ofNat (s.lhs[s.focus]'(by
        rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
        simpa [hlhs] using hfocus)))) := by
    have hLhsLookupX := skyReducerAppXLoadedState_lookup_lhs s oracleVals hwf hfocus
    have hFocusLookupX := skyReducerAppXLoadedState_lookup_focus s oracleVals hwf hfocus
    have hReadPtrX :
        (skyReducerAppXLoadedState s oracleVals hwf hfocus).readPtr
          { block := 0, offset := Int.ofNat ((layoutForState s oracleVals).lhsBase + s.focus) } =
        (skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.read
          ((layoutForState s oracleVals).lhsBase + s.focus) := by
      simpa using
        (CState.readPtr_block0 (skyReducerAppXLoadedState s oracleVals hwf hfocus)
          ((layoutForState s oracleVals).lhsBase + s.focus)
          ((layoutForState s oracleVals).lhsBase + s.focus))
    have hloadX :
        evalExpr (SKYLowering.loadAt "lhs" (.var "focus"))
            (skyReducerAppXLoadedState s oracleVals hwf hfocus) =
          (skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.read
            ((layoutForState s oracleVals).lhsBase + s.focus) := by
      simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hLhsLookupX, hFocusLookupX, hAdd] using
        hReadPtrX
    rw [← hloadX]
    exact skyReducerAppXLoadedState_eval_lhsAtFocus s oracleVals hwf hfocus
  rw [hload, hReadOther]
  exact hReadX

theorem execStmt_appLoadFocus_afterStore
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 3
      (.assign (.var "focus") (SKYLowering.loadAt "lhs" (.var "focus")))
      (skyReducerAppStoredState s oracleVals hwf hfocus) =
        some (.normal (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus)) := by
  simp [execStmt, skyReducerAppFocusUpdatedState, skyReducerAppFocusVal,
    skyReducerAppStoredState_eval_lhsAtFocus]

theorem skyReducerAppFocusUpdatedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerAppFocusUpdatedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppStoredState s oracleVals hwf hfocus) "focus" "stackSize"
      (skyReducerAppFocusVal s hwf hfocus) (by decide : "stackSize" ≠ "focus"))

theorem execStmt_appIncStackSize_afterFocus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 2
      (.assign (.var "stackSize") (.binop .add (.var "stackSize") (.intLit 1)))
      (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus) =
        some (.normal (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus)) := by
  have hEval :
      evalExpr (.binop .add (.var "stackSize") (.intLit 1))
        (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus) =
      some (.int (Int.ofNat (s.stack.length + 1))) := by
    simp [evalExpr, evalStaticExpr, skyReducerAppFocusUpdatedState_lookup_stackSize]
  simp [execStmt, skyReducerAppStackSizeUpdatedState, hEval]

theorem skyReducerAppStoredState_lookup_focusPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStoredState s oracleVals hwf hfocus).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  simpa [skyReducerAppStoredState] using
    (skyReducerAppXLoadedState_lookup_focusPtr s oracleVals hwf hfocus)

theorem skyReducerAppStoredState_lookup_stackSizePtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStoredState s oracleVals hwf hfocus).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  simpa [skyReducerAppStoredState] using
    (skyReducerAppXLoadedState_lookup_stackSizePtr s oracleVals hwf hfocus)

theorem skyReducerAppStoredState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStoredState s oracleVals hwf hfocus).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  simpa [skyReducerAppStoredState] using
    (skyReducerAppXLoadedState_lookup_nodeCountPtr s oracleVals hwf hfocus)

theorem skyReducerAppStoredState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStoredState s oracleVals hwf hfocus).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  simpa [skyReducerAppStoredState] using
    (skyReducerAppXLoadedState_lookup_nodeCount s oracleVals hwf hfocus)

theorem skyReducerAppStackSizeUpdatedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).lookupVar "focus" =
      some (skyReducerAppFocusVal s hwf hfocus) := by
  rw [skyReducerAppStackSizeUpdatedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus) "stackSize" "focus"
      (.int (Int.ofNat (s.stack.length + 1))) (by decide : "focus" ≠ "stackSize"))

theorem skyReducerAppStackSizeUpdatedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).lookupVar "stackSize" =
      some (.int (Int.ofNat (s.stack.length + 1))) := by
  rw [skyReducerAppStackSizeUpdatedState]
  simpa using
    (lookupVar_updateVar_eq (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus) "stackSize"
      (.int (Int.ofNat (s.stack.length + 1))))

theorem skyReducerAppStackSizeUpdatedState_lookup_focusPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  rw [skyReducerAppStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focusPtr" (.int (Int.ofNat (s.stack.length + 1))) (by decide)]
  rw [skyReducerAppFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "focusPtr" (skyReducerAppFocusVal s hwf hfocus) (by decide)]
  exact skyReducerAppStoredState_lookup_focusPtr s oracleVals hwf hfocus

theorem skyReducerAppStackSizeUpdatedState_lookup_stackSizePtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  rw [skyReducerAppStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stackSizePtr" (.int (Int.ofNat (s.stack.length + 1))) (by decide)]
  rw [skyReducerAppFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "stackSizePtr" (skyReducerAppFocusVal s hwf hfocus) (by decide)]
  exact skyReducerAppStoredState_lookup_stackSizePtr s oracleVals hwf hfocus

theorem skyReducerAppStackSizeUpdatedState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  rw [skyReducerAppStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCountPtr" (.int (Int.ofNat (s.stack.length + 1))) (by decide)]
  rw [skyReducerAppFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCountPtr" (skyReducerAppFocusVal s hwf hfocus) (by decide)]
  exact skyReducerAppStoredState_lookup_nodeCountPtr s oracleVals hwf hfocus

theorem skyReducerAppStackSizeUpdatedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerAppStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCount" (.int (Int.ofNat (s.stack.length + 1))) (by decide)]
  rw [skyReducerAppFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCount" (skyReducerAppFocusVal s hwf hfocus) (by decide)]
  exact skyReducerAppStoredState_lookup_nodeCount s oracleVals hwf hfocus

theorem execStmt_appWriteFocusPtr_afterStackSize
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 2 (SKYLowering.writeScalar "focusPtr" (.var "focus"))
      (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus) =
        some (.normal (skyReducerAppCommittedFocusState s oracleVals hwf hfocus)) := by
  simpa [skyReducerAppCommittedFocusState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus) "focusPtr" "focus"
      (layoutForState s oracleVals).focusBase (skyReducerAppFocusVal s hwf hfocus)
      (skyReducerAppStackSizeUpdatedState_lookup_focusPtr s oracleVals hwf hfocus)
      (skyReducerAppStackSizeUpdatedState_lookup_focus s oracleVals hwf hfocus))

theorem execStmt_appWriteStackSizePtr_afterFocusPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 2 (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
      (skyReducerAppCommittedFocusState s oracleVals hwf hfocus) =
        some (.normal (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus)) := by
  have hPtr :
      (skyReducerAppCommittedFocusState s oracleVals hwf hfocus).lookupVar "stackSizePtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
    simpa [skyReducerAppCommittedFocusState] using
      (skyReducerAppStackSizeUpdatedState_lookup_stackSizePtr s oracleVals hwf hfocus)
  have hVal :
      (skyReducerAppCommittedFocusState s oracleVals hwf hfocus).lookupVar "stackSize" =
        some (.int (Int.ofNat (s.stack.length + 1))) := by
    simpa [skyReducerAppCommittedFocusState] using
      (skyReducerAppStackSizeUpdatedState_lookup_stackSize s oracleVals hwf hfocus)
  simpa [skyReducerAppCommittedStackSizeState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerAppCommittedFocusState s oracleVals hwf hfocus) "stackSizePtr" "stackSize"
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length + 1)))
      hPtr hVal)

theorem execStmt_appWriteNodeCountPtr_afterStackSizePtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 2 (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
      (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus) =
        some (.normal (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
  have hPtr :
      (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).lookupVar "nodeCountPtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
    simpa [skyReducerAppCommittedStackSizeState, skyReducerAppCommittedFocusState] using
      (skyReducerAppStackSizeUpdatedState_lookup_nodeCountPtr s oracleVals hwf hfocus)
  have hVal :
      (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerAppCommittedStackSizeState, skyReducerAppCommittedFocusState] using
      (skyReducerAppStackSizeUpdatedState_lookup_nodeCount s oracleVals hwf hfocus)
  simpa [skyReducerAppCommittedState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus) "nodeCountPtr" "nodeCount"
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))
      hPtr hVal)

theorem execStmt_appCommit_afterStackSize
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 4 (SKYLowering.commitAndReturn .progress)
      (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus) =
        some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
  calc
    execStmt 4 (SKYLowering.commitAndReturn .progress)
        (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus)
      = execStmt 3
          (.seq
            (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
            (.seq
              (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
              (.ret (.intLit StepStatus.progress.code))))
          (skyReducerAppCommittedFocusState s oracleVals hwf hfocus) := by
            exact execStmt_seq_of_normal 3
              (SKYLowering.writeScalar "focusPtr" (.var "focus"))
              (.seq
                (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
                (.seq
                  (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
                  (.ret (.intLit StepStatus.progress.code))))
              (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus)
              (skyReducerAppCommittedFocusState s oracleVals hwf hfocus)
              (execStmt_appWriteFocusPtr_afterStackSize s oracleVals hwf hfocus)
    _ = execStmt 2
          (.seq
            (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
            (.ret (.intLit StepStatus.progress.code)))
          (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus) := by
            exact execStmt_seq_of_normal 2
              (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
              (.seq
                (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
                (.ret (.intLit StepStatus.progress.code)))
              (skyReducerAppCommittedFocusState s oracleVals hwf hfocus)
              (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus)
              (execStmt_appWriteStackSizePtr_afterFocusPtr s oracleVals hwf hfocus)
    _ = execStmt 1
          (.ret (.intLit StepStatus.progress.code))
          (skyReducerAppCommittedState s oracleVals hwf hfocus) := by
            exact execStmt_seq_of_normal 1
              (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
              (.ret (.intLit StepStatus.progress.code))
              (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus)
              (skyReducerAppCommittedState s oracleVals hwf hfocus)
              (execStmt_appWriteNodeCountPtr_afterStackSizePtr s oracleVals hwf hfocus)
    _ = some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
          simp [execStmt, evalExpr, evalStaticExpr]

theorem skyReducerScalarsLoadedState_eval_rhsAtFocus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    evalExpr (SKYLowering.loadAt "rhs" (.var "focus")) (skyReducerScalarsLoadedState s oracleVals) =
      some (.int (Int.ofNat (s.rhs[s.focus]'(by
        rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
        simpa [hrhs] using hfocus)))) := by
  rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, _hstack⟩
  have hfocusMax : s.focus < s.maxNodes := Nat.lt_of_lt_of_le hfocus hnodes
  have hRhsPtr := skyReducerScalarsLoadedState_lookup_rhs s oracleVals
  have hFocusVar := skyReducerScalarsLoadedState_lookup_focus s oracleVals
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase))
        (.int (Int.ofNat s.focus)) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).rhsBase + s.focus))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).rhsBase : Int) + ↑s.focus := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).rhsBase : Int) + ↑s.focus then
        some (CVal.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase + Int.ofNat s.focus))
      else none) = some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).rhsBase + s.focus)))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerScalarsLoadedState s oracleVals).readPtr
        { block := 0, offset := Int.ofNat ((layoutForState s oracleVals).rhsBase + s.focus) } =
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).rhsBase + s.focus) := by
    simpa using
      (CState.readPtr_block0 (skyReducerScalarsLoadedState s oracleVals)
        ((layoutForState s oracleVals).rhsBase + s.focus)
        ((layoutForState s oracleVals).rhsBase + s.focus))
  have hload :
      evalExpr (SKYLowering.loadAt "rhs" (.var "focus")) (skyReducerScalarsLoadedState s oracleVals) =
        (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).rhsBase + s.focus) := by
    simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hRhsPtr, hFocusVar, hAdd] using hReadPtr
  have hcell :
      readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
        (s.maxNodes + s.maxNodes + s.focus) =
        some (s.rhs[s.focus]'(by simpa [hrhs] using hfocus)) := by
    let h0 := writeIntList Heap.empty 0 s.tags.toList
    let h1 := writeNatList h0 s.maxNodes s.lhs.toList
    let h2 := writeNatList h1 (s.maxNodes + s.maxNodes) s.rhs.toList
    let h3 := writeNatList h2 (s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList
    let h4 := writeIntList h3 (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes)
      (oracleValuesPadded s oracleVals)
    let h5 := writeNatList h4
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals) s.stack.reverse
    let h6 := h5.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
      (.int (Int.ofNat s.focus))
    let h7 := h6.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
      (.int (Int.ofNat s.stack.length))
    let h8 := h7.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1)
      (.int (Int.ofNat s.nodeCount))
    have hcell' :
        readNatCell? h8 (s.maxNodes + s.maxNodes + s.focus) =
          some (s.rhs[s.focus]'(by simpa [hrhs] using hfocus)) := by
      simp only [h8, h7, h6]
      have hrhsAddrNeNodeCountBase :
          s.maxNodes + s.maxNodes + s.focus ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ hrhsAddrNeNodeCountBase]
      have hrhsAddrNeStackSizeBase :
          s.maxNodes + s.maxNodes + s.focus ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ hrhsAddrNeStackSizeBase]
      have hrhsAddrNeFocusBase :
          s.maxNodes + s.maxNodes + s.focus ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) := by
        omega
      rw [readNatCell?_write_other _ _ _ _ hrhsAddrNeFocusBase]
      have hstackBefore :
          s.maxNodes + s.maxNodes + s.focus <
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals := by
        omega
      rw [writeNatList_read_before _ _ _ _ hstackBefore]
      have horacleBefore :
          s.maxNodes + s.maxNodes + s.focus < s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes := by
        omega
      rw [writeIntList_readNat_before _ _ _ _ horacleBefore]
      have hrefsBefore : s.maxNodes + s.maxNodes + s.focus < s.maxNodes + s.maxNodes + s.maxNodes := by
        omega
      rw [writeNatList_read_before _ _ _ _ hrefsBefore]
      simpa [h2, h1, h0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (readNatCell?_writeNatList_at
          (heap := h1) (base := s.maxNodes + s.maxNodes) (xs := s.rhs.toList)
          (i := s.focus) (by simpa [hrhs] using hfocus))
    simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, encodeHeapWithLayout, encodeStackWithLayout,
      encodeOracleValuesWithLayout, encodeNodeArraysWithLayout, layoutForState, layoutFor, State.nodeCount]
      using hcell'
  have hheap :
      (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).rhsBase + s.focus) =
        some (.int (Int.ofNat (s.rhs[s.focus]'(by simpa [hrhs] using hfocus)))) := by
    have hheapEnc :
        (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
          (s.maxNodes + s.maxNodes + s.focus) =
            some (.int (Int.ofNat (s.rhs[s.focus]'(by simpa [hrhs] using hfocus)))) := by
      cases hread :
          (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
            (s.maxNodes + s.maxNodes + s.focus) with
      | none =>
          simp [readNatCell?, readIntCell?, hread] at hcell
      | some v =>
          cases v with
          | int n =>
              simp [readNatCell?, readIntCell?, hread] at hcell
              have hn :
                  n = Int.ofNat (s.rhs[s.focus]'(by simpa [hrhs] using hfocus)) := by
                calc
                  n = Int.ofNat n.toNat := by
                    symm
                    exact Int.toNat_of_nonneg hcell.1
                  _ = Int.ofNat (s.rhs[s.focus]'(by simpa [hrhs] using hfocus)) := by
                    simp [hcell.2]
              simp [hread, hn]
          | ptr block offset =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | uint n sz =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | float v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | null =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | undef =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | structVal fields =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | unionVal tag v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
    simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
      skyReducerEntry, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
      encodeExecStateWithLayout, layoutForState, layoutFor] using hheapEnc
  rw [hload, hheap]

theorem skyReducerScalarsLoadedState_eval_oracleRefAtFocus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    evalExpr (SKYLowering.loadAt "oracleRefs" (.var "focus")) (skyReducerScalarsLoadedState s oracleVals) =
      some (.int (Int.ofNat (s.oracleRefs[s.focus]'(by
        rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
        simpa [hrefs] using hfocus)))) := by
  rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, _hstack⟩
  have hfocusMax : s.focus < s.maxNodes := Nat.lt_of_lt_of_le hfocus hnodes
  have hRefsPtr := skyReducerScalarsLoadedState_lookup_oracleRefs s oracleVals
  have hFocusVar := skyReducerScalarsLoadedState_lookup_focus s oracleVals
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase))
        (.int (Int.ofNat s.focus)) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).refsBase + s.focus))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).refsBase : Int) + ↑s.focus := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).refsBase : Int) + ↑s.focus then
        some (CVal.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase + Int.ofNat s.focus))
      else none) = some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).refsBase + s.focus)))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerScalarsLoadedState s oracleVals).readPtr
        { block := 0, offset := Int.ofNat ((layoutForState s oracleVals).refsBase + s.focus) } =
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).refsBase + s.focus) := by
    simpa using
      (CState.readPtr_block0 (skyReducerScalarsLoadedState s oracleVals)
        ((layoutForState s oracleVals).refsBase + s.focus)
        ((layoutForState s oracleVals).refsBase + s.focus))
  have hload :
      evalExpr (SKYLowering.loadAt "oracleRefs" (.var "focus")) (skyReducerScalarsLoadedState s oracleVals) =
        (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).refsBase + s.focus) := by
    simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hRefsPtr, hFocusVar, hAdd] using hReadPtr
  have hcell :
      readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
        (s.maxNodes + s.maxNodes + s.maxNodes + s.focus) =
        some (s.oracleRefs[s.focus]'(by simpa [hrefs] using hfocus)) := by
    let h0 := writeIntList Heap.empty 0 s.tags.toList
    let h1 := writeNatList h0 s.maxNodes s.lhs.toList
    let h2 := writeNatList h1 (s.maxNodes + s.maxNodes) s.rhs.toList
    let h3 := writeNatList h2 (s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList
    let h4 := writeIntList h3 (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes)
      (oracleValuesPadded s oracleVals)
    let h5 := writeNatList h4
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals) s.stack.reverse
    let h6 := h5.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
      (.int (Int.ofNat s.focus))
    let h7 := h6.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
      (.int (Int.ofNat s.stack.length))
    let h8 := h7.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1)
      (.int (Int.ofNat s.nodeCount))
    have hcell' :
        readNatCell? h8 (s.maxNodes + s.maxNodes + s.maxNodes + s.focus) =
          some (s.oracleRefs[s.focus]'(by simpa [hrefs] using hfocus)) := by
      simp only [h8, h7, h6]
      have hrefsAddrNeNodeCountBase :
          s.maxNodes + s.maxNodes + s.maxNodes + s.focus ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ hrefsAddrNeNodeCountBase]
      have hrefsAddrNeStackSizeBase :
          s.maxNodes + s.maxNodes + s.maxNodes + s.focus ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ hrefsAddrNeStackSizeBase]
      have hrefsAddrNeFocusBase :
          s.maxNodes + s.maxNodes + s.maxNodes + s.focus ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) := by
        omega
      rw [readNatCell?_write_other _ _ _ _ hrefsAddrNeFocusBase]
      have hstackBefore :
          s.maxNodes + s.maxNodes + s.maxNodes + s.focus <
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals := by
        omega
      rw [writeNatList_read_before _ _ _ _ hstackBefore]
      have horacleBefore :
          s.maxNodes + s.maxNodes + s.maxNodes + s.focus <
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes := by
        omega
      rw [writeIntList_readNat_before _ _ _ _ horacleBefore]
      simpa [h3, h2, h1, h0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (readNatCell?_writeNatList_at
          (heap := h2) (base := s.maxNodes + s.maxNodes + s.maxNodes) (xs := s.oracleRefs.toList)
          (i := s.focus) (by simpa [hrefs] using hfocus))
    simpa [encodeHeapWithLayout, encodeStackWithLayout, encodeOracleValuesWithLayout,
      encodeNodeArraysWithLayout, layoutForState, layoutFor, State.nodeCount] using hcell'
  have hheap :
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).refsBase + s.focus) =
      some (.int (Int.ofNat (s.oracleRefs[s.focus]'(by simpa [hrefs] using hfocus)))) := by
    have hheapEnc :
        (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
          (s.maxNodes + s.maxNodes + s.maxNodes + s.focus) =
            some (.int (Int.ofNat (s.oracleRefs[s.focus]'(by simpa [hrefs] using hfocus)))) := by
      cases hread :
          (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
            (s.maxNodes + s.maxNodes + s.maxNodes + s.focus) with
      | none =>
          simp [readNatCell?, readIntCell?, hread] at hcell
      | some v =>
          cases v with
          | int n =>
              simp [readNatCell?, readIntCell?, hread] at hcell
              have hn :
                  n = Int.ofNat (s.oracleRefs[s.focus]'(by simpa [hrefs] using hfocus)) := by
                calc
                  n = Int.ofNat n.toNat := by
                    symm
                    exact Int.toNat_of_nonneg hcell.1
                  _ = Int.ofNat (s.oracleRefs[s.focus]'(by simpa [hrefs] using hfocus)) := by
                    simp [hcell.2]
              simp [hread, hn]
          | ptr block offset =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | uint n sz =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | float v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | null =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | undef =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | structVal fields =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | unionVal tag v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
    simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
      skyReducerEntry, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
      encodeExecStateWithLayout, layoutForState, layoutFor] using hheapEnc
  rw [hload, hheap]

theorem execStmt_loadTag_skyReducerScalarsLoaded
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 5 (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.normal ((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus)))) := by
  simp [execStmt, skyReducerScalarsLoadedState_eval_tagAtFocus, hwf, hfocus]

theorem execStmt_tagSwitch_app_of_tagLoaded
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app) :
    execStmt 5
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      ((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))) =
        execStmt 4 SKYLowering.appCase
          ((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))) := by
  simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
    lookupVar_updateVar_eq, happ, NodeTag.code]

theorem execStmt_appTagPrefix_skyReducerScalarsLoaded
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    (happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app) :
    execStmt 6
      (.seq
        (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted)))
      (skyReducerScalarsLoadedState s oracleVals) =
        execStmt 4 SKYLowering.appCase
          ((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))) := by
  calc
    execStmt 6
        (.seq
          (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted)))
        (skyReducerScalarsLoadedState s oracleVals)
      = execStmt 5
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          ((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))) := by
            exact execStmt_seq_of_normal
              (fuel := 5)
              (s1 := (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus"))))
              (s2 := switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted))
              (st := skyReducerScalarsLoadedState s oracleVals)
              (st' := (skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus)))
              (h := execStmt_loadTag_skyReducerScalarsLoaded s oracleVals hwf hfocus)
    _ = execStmt 4 SKYLowering.appCase
          ((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))) := by
            exact execStmt_tagSwitch_app_of_tagLoaded s oracleVals hfocus happ

theorem execStmt_appLoadX_tagLoaded
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 5
      (.assign (.var "x") (SKYLowering.loadAt "rhs" (.var "focus")))
      ((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))) =
        some (.normal
          (((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))).updateVar
            "x" (.int (Int.ofNat (s.rhs[s.focus]'(by
              rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
              simpa [hrhs] using hfocus)))))) := by
  have hRhsLookup :
      (((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))).lookupVar "rhs") =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
    simpa using
      (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "rhs"
        (.int (s.tags[s.focus]'hfocus)) (by decide : "rhs" ≠ "tag"))
  have hFocusLookup :
      (((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))).lookupVar "focus") =
        some (.int (Int.ofNat s.focus)) := by
    simpa using
      (lookupVar_updateVar_ne (skyReducerScalarsLoadedState s oracleVals) "tag" "focus"
        (.int (s.tags[s.focus]'hfocus)) (by decide : "focus" ≠ "tag"))
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase))
        (.int (Int.ofNat s.focus)) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).rhsBase + s.focus))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).rhsBase : Int) + ↑s.focus := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).rhsBase : Int) + ↑s.focus then
        some (CVal.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase + Int.ofNat s.focus))
      else none) = some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).rhsBase + s.focus)))
    simp [hnonneg]
  have hReadPtr :
      (((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))).readPtr
        { block := 0, offset := Int.ofNat ((layoutForState s oracleVals).rhsBase + s.focus) }) =
      (((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))).heap.read
        ((layoutForState s oracleVals).rhsBase + s.focus)) := by
    simpa using
      (CState.readPtr_block0
        (((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))))
        ((layoutForState s oracleVals).rhsBase + s.focus)
        ((layoutForState s oracleVals).rhsBase + s.focus))
  have hHeapSame :
      (((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))).heap.read
        ((layoutForState s oracleVals).rhsBase + s.focus)) =
      ((skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).rhsBase + s.focus)) := by
    simp [updateVar_heap]
  have hEval :
      evalExpr (SKYLowering.loadAt "rhs" (.var "focus"))
        ((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))) =
          some (.int (Int.ofNat (s.rhs[s.focus]'(by
            rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
            simpa [hrhs] using hfocus)))) := by
    calc
      evalExpr (SKYLowering.loadAt "rhs" (.var "focus"))
          ((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus)))
        = (((skyReducerScalarsLoadedState s oracleVals).updateVar "tag" (.int (s.tags[s.focus]'hfocus))).heap.read
            ((layoutForState s oracleVals).rhsBase + s.focus)) := by
              simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hRhsLookup, hFocusLookup, hAdd] using hReadPtr
      _ = ((skyReducerScalarsLoadedState s oracleVals).heap.read
            ((layoutForState s oracleVals).rhsBase + s.focus)) := hHeapSame
      _ = some (.int (Int.ofNat (s.rhs[s.focus]'(by
            rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
            simpa [hrhs] using hfocus)))) := by
              simpa using skyReducerScalarsLoadedState_eval_rhsAtFocus s oracleVals hwf hfocus
  simp [execStmt, hEval]

theorem execStmt_appLoadX_tagLoaded'
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 5
      (.assign (.var "x") (SKYLowering.loadAt "rhs" (.var "focus")))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.normal (skyReducerAppXLoadedState s oracleVals hwf hfocus)) := by
  simpa [skyReducerAppTagLoadedState, skyReducerAppXLoadedState] using
    execStmt_appLoadX_tagLoaded s oracleVals hwf hfocus

theorem execStmt_appStoreStack_afterLoadX
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 4
      (SKYLowering.storeAt "stack" (.var "stackSize") (.var "x"))
      (skyReducerAppXLoadedState s oracleVals hwf hfocus) =
        some (.normal (skyReducerAppStoredState s oracleVals hwf hfocus)) := by
  have hStackLookup :
      (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "stack" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
    exact skyReducerAppXLoadedState_lookup_stack s oracleVals hwf hfocus
  have hStackSizeLookup :
      (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "stackSize" =
        some (.int (Int.ofNat s.stack.length)) := by
    exact skyReducerAppXLoadedState_lookup_stackSize s oracleVals hwf hfocus
  have hXLookup :
      (skyReducerAppXLoadedState s oracleVals hwf hfocus).lookupVar "x" =
        some (skyReducerAppXVal s hwf hfocus) := by
    exact skyReducerAppXLoadedState_lookup_x s oracleVals hwf hfocus
  have hAddr :
      evalExpr (.binop .add (.var "stack") (.var "stackSize"))
        (skyReducerAppXLoadedState s oracleVals hwf hfocus) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + s.stack.length))) := by
    have hAdd :
        evalBinOp .add
          (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase))
          (.int (Int.ofNat s.stack.length)) =
        some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + s.stack.length))) := by
      have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑s.stack.length := by
        omega
      change
        (if 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑s.stack.length then
          some (CVal.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase + Int.ofNat s.stack.length))
        else none) =
          some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + s.stack.length)))
      simp [hnonneg]
    calc
      evalExpr (.binop .add (.var "stack") (.var "stackSize"))
          (skyReducerAppXLoadedState s oracleVals hwf hfocus)
        = evalBinOp .add
            (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase))
            (.int (Int.ofNat s.stack.length)) := by
              simp [evalExpr, evalStaticExpr, hStackLookup, hStackSizeLookup]
      _ = some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + s.stack.length))) := hAdd
  have hWritePtr :
      (skyReducerAppXLoadedState s oracleVals hwf hfocus).writePtr
        { block := 0
          offset := Int.ofNat (layoutForState s oracleVals).stackBase + Int.ofNat s.stack.length }
        (skyReducerAppXVal s hwf hfocus) =
      some (skyReducerAppStoredState s oracleVals hwf hfocus) := by
    simpa [skyReducerAppStoredState] using
      (CState.writePtr_block0
        (skyReducerAppXLoadedState s oracleVals hwf hfocus)
        ((layoutForState s oracleVals).stackBase + s.stack.length)
        ((layoutForState s oracleVals).stackBase + s.stack.length)
        (skyReducerAppXVal s hwf hfocus))
  calc
    execStmt 4
        (SKYLowering.storeAt "stack" (.var "stackSize") (.var "x"))
        (skyReducerAppXLoadedState s oracleVals hwf hfocus)
      = Option.map ExecResult.normal
          ((skyReducerAppXLoadedState s oracleVals hwf hfocus).writePtr
            { block := 0
              offset := Int.ofNat (layoutForState s oracleVals).stackBase + Int.ofNat s.stack.length }
            (skyReducerAppXVal s hwf hfocus)) := by
              simp [execStmt, SKYLowering.storeAt, evalExpr, evalStaticExpr, hXLookup, hAddr]
    _ = some (.normal (skyReducerAppStoredState s oracleVals hwf hfocus)) := by
          simpa using congrArg (Option.map ExecResult.normal) hWritePtr

theorem execStmt_appCase_tagLoaded
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    execStmt 8 SKYLowering.appCase
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
  calc
    execStmt 8 SKYLowering.appCase
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 7
          (.seq
            (SKYLowering.storeAt "stack" (.var "stackSize") (.var "x"))
            (.seq
              (.assign (.var "focus") (SKYLowering.loadAt "lhs" (.var "focus")))
              (.seq
                (.assign (.var "stackSize") (.binop .add (.var "stackSize") (.intLit 1)))
                (SKYLowering.commitAndReturn .progress))))
          (skyReducerAppXLoadedState s oracleVals hwf hfocus) := by
            simpa [SKYLowering.appCase, SKYLowering.seqs] using
              (execStmt_seq_of_normal 7
                (.assign (.var "x") (SKYLowering.loadAt "rhs" (.var "focus")))
                (.seq
                  (SKYLowering.storeAt "stack" (.var "stackSize") (.var "x"))
                  (.seq
                    (.assign (.var "focus") (SKYLowering.loadAt "lhs" (.var "focus")))
                    (.seq
                      (.assign (.var "stackSize") (.binop .add (.var "stackSize") (.intLit 1)))
                      (SKYLowering.commitAndReturn .progress))))
                (skyReducerAppTagLoadedState s oracleVals hfocus)
                (skyReducerAppXLoadedState s oracleVals hwf hfocus)
                (by simpa [execStmt] using execStmt_appLoadX_tagLoaded' s oracleVals hwf hfocus))
    _ = execStmt 6
          (.seq
            (.assign (.var "focus") (SKYLowering.loadAt "lhs" (.var "focus")))
            (.seq
              (.assign (.var "stackSize") (.binop .add (.var "stackSize") (.intLit 1)))
              (SKYLowering.commitAndReturn .progress)))
          (skyReducerAppStoredState s oracleVals hwf hfocus) := by
            exact execStmt_seq_of_normal 6
              (SKYLowering.storeAt "stack" (.var "stackSize") (.var "x"))
              (.seq
                (.assign (.var "focus") (SKYLowering.loadAt "lhs" (.var "focus")))
                (.seq
                  (.assign (.var "stackSize") (.binop .add (.var "stackSize") (.intLit 1)))
                  (SKYLowering.commitAndReturn .progress)))
              (skyReducerAppXLoadedState s oracleVals hwf hfocus)
              (skyReducerAppStoredState s oracleVals hwf hfocus)
              (by simpa [execStmt] using execStmt_appStoreStack_afterLoadX s oracleVals hwf hfocus)
    _ = execStmt 5
          (.seq
            (.assign (.var "stackSize") (.binop .add (.var "stackSize") (.intLit 1)))
            (SKYLowering.commitAndReturn .progress))
          (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus) := by
            exact execStmt_seq_of_normal 5
              (.assign (.var "focus") (SKYLowering.loadAt "lhs" (.var "focus")))
              (.seq
                (.assign (.var "stackSize") (.binop .add (.var "stackSize") (.intLit 1)))
                (SKYLowering.commitAndReturn .progress))
              (skyReducerAppStoredState s oracleVals hwf hfocus)
              (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus)
              (by simpa [execStmt] using execStmt_appLoadFocus_afterStore s oracleVals hwf hfocus)
    _ = execStmt 4 (SKYLowering.commitAndReturn .progress)
          (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus) := by
            exact execStmt_seq_of_normal 4
              (.assign (.var "stackSize") (.binop .add (.var "stackSize") (.intLit 1)))
              (SKYLowering.commitAndReturn .progress)
              (skyReducerAppFocusUpdatedState s oracleVals hwf hfocus)
              (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus)
              (by simpa [execStmt] using execStmt_appIncStackSize_afterFocus s oracleVals hwf hfocus)
    _ = some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
          exact execStmt_appCommit_afterStackSize s oracleVals hwf hfocus

theorem execStmt_tagSwitch_app_of_tagLoaded_committed
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    (happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app) :
    execStmt 9
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
  calc
    execStmt 9
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted))
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 8 SKYLowering.appCase
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
              skyReducerAppTagLoadedState, lookupVar_updateVar_eq, happ, NodeTag.code]
    _ = some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
          exact execStmt_appCase_tagLoaded s oracleVals hwf hfocus

theorem execStmt_appTagPrefix_skyReducerScalarsLoaded_committed
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    (happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app) :
    execStmt 10
      (.seq
        (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted)))
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
  calc
    execStmt 10
        (.seq
          (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted)))
        (skyReducerScalarsLoadedState s oracleVals)
      = execStmt 9
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            exact execStmt_seq_of_normal 9
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted))
              (skyReducerScalarsLoadedState s oracleVals)
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (by
                simpa [execStmt, skyReducerAppTagLoadedState] using
                  execStmt_loadTag_skyReducerScalarsLoaded s oracleVals hwf hfocus)
    _ = some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
          exact execStmt_tagSwitch_app_of_tagLoaded_committed s oracleVals hwf hfocus happ

theorem execStmt_focusOutOfRange_skyReducerEntry
    (s : State) (oracleVals : Array Int) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt 14
      (.seq
        (.assign (.var "focus") (.deref (.var "focusPtr")))
        (.seq
          (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))))
      (skyReducerEntry s oracleVals) =
        execStmt 10 (SKYLowering.commitAndReturn .halted)
          (skyReducerScalarsLoadedState s oracleVals) := by
  calc
    execStmt 14
        (.seq
          (.assign (.var "focus") (.deref (.var "focusPtr")))
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted)))))
        (skyReducerEntry s oracleVals)
      = execStmt 13
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))))
          (skyReducerFocusLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 13
              (.assign (.var "focus") (.deref (.var "focusPtr")))
              (.seq
                (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                (.seq
                  (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                  (.ite
                    (.binop .lt (.var "focus") (.var "nodeCount"))
                    (.seq
                      (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                      (switchMany (.var "tag")
                        [ (NodeTag.code .app, SKYLowering.appCase)
                        , (NodeTag.code .combK, SKYLowering.kCase)
                        , (NodeTag.code .combS, SKYLowering.sCase)
                        , (NodeTag.code .combY, SKYLowering.yCase)
                        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                        (SKYLowering.commitAndReturn .halted)))
                    (SKYLowering.commitAndReturn .halted))))
              (skyReducerEntry s oracleVals)
              (skyReducerFocusLoadedState s oracleVals)
              (by simpa [execStmt, skyReducerFocusLoadedState] using execStmt_loadFocus_skyReducerEntry s oracleVals)
    _ = execStmt 12
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerStackSizeLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 12
              (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
              (.seq
                (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                (.ite
                  (.binop .lt (.var "focus") (.var "nodeCount"))
                  (.seq
                    (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                    (switchMany (.var "tag")
                      [ (NodeTag.code .app, SKYLowering.appCase)
                      , (NodeTag.code .combK, SKYLowering.kCase)
                      , (NodeTag.code .combS, SKYLowering.sCase)
                      , (NodeTag.code .combY, SKYLowering.yCase)
                      , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                      (SKYLowering.commitAndReturn .halted)))
                  (SKYLowering.commitAndReturn .halted)))
              (skyReducerFocusLoadedState s oracleVals)
              (skyReducerStackSizeLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals)
    _ = execStmt 11
          (.ite
            (.binop .lt (.var "focus") (.var "nodeCount"))
            (.seq
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted)))
            (SKYLowering.commitAndReturn .halted))
          (skyReducerScalarsLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 11
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))
              (skyReducerStackSizeLoadedState s oracleVals)
              (skyReducerScalarsLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals)
    _ = execStmt 10 (SKYLowering.commitAndReturn .halted)
          (skyReducerScalarsLoadedState s oracleVals) := by
            exact execStmt_guard_false_skyReducerScalarsLoaded_fuel 6 s oracleVals
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)
              hfocus

theorem execStmt_appPath_skyReducerEntry
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app) :
    execStmt 14
      (.seq
        (.assign (.var "focus") (.deref (.var "focusPtr")))
        (.seq
          (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))))
      (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
  calc
    execStmt 14
        (.seq
          (.assign (.var "focus") (.deref (.var "focusPtr")))
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted)))))
        (skyReducerEntry s oracleVals)
      = execStmt 13
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))))
          (skyReducerFocusLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 13
              (.assign (.var "focus") (.deref (.var "focusPtr")))
              (.seq
                (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                (.seq
                  (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                  (.ite
                    (.binop .lt (.var "focus") (.var "nodeCount"))
                    (.seq
                      (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                      (switchMany (.var "tag")
                        [ (NodeTag.code .app, SKYLowering.appCase)
                        , (NodeTag.code .combK, SKYLowering.kCase)
                        , (NodeTag.code .combS, SKYLowering.sCase)
                        , (NodeTag.code .combY, SKYLowering.yCase)
                        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                        (SKYLowering.commitAndReturn .halted)))
                    (SKYLowering.commitAndReturn .halted))))
              (skyReducerEntry s oracleVals)
              (skyReducerFocusLoadedState s oracleVals)
              (by simpa [execStmt, skyReducerFocusLoadedState] using execStmt_loadFocus_skyReducerEntry s oracleVals)
    _ = execStmt 12
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerStackSizeLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 12
              (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
              (.seq
                (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                (.ite
                  (.binop .lt (.var "focus") (.var "nodeCount"))
                  (.seq
                    (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                    (switchMany (.var "tag")
                      [ (NodeTag.code .app, SKYLowering.appCase)
                      , (NodeTag.code .combK, SKYLowering.kCase)
                      , (NodeTag.code .combS, SKYLowering.sCase)
                      , (NodeTag.code .combY, SKYLowering.yCase)
                      , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                      (SKYLowering.commitAndReturn .halted)))
                  (SKYLowering.commitAndReturn .halted)))
              (skyReducerFocusLoadedState s oracleVals)
              (skyReducerStackSizeLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals)
    _ = execStmt 11
          (.ite
            (.binop .lt (.var "focus") (.var "nodeCount"))
            (.seq
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted)))
            (SKYLowering.commitAndReturn .halted))
          (skyReducerScalarsLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 11
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))
              (skyReducerStackSizeLoadedState s oracleVals)
              (skyReducerScalarsLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals)
    _ = execStmt 10
          (.seq
            (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
            (switchMany (.var "tag")
              [ (NodeTag.code .app, SKYLowering.appCase)
              , (NodeTag.code .combK, SKYLowering.kCase)
              , (NodeTag.code .combS, SKYLowering.sCase)
              , (NodeTag.code .combY, SKYLowering.yCase)
              , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerScalarsLoadedState s oracleVals) := by
            rw [execStmt_ite_of_eval_true
              (fuel := 10) (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
              (th := (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted))))
              (el := SKYLowering.commitAndReturn .halted)
              (st := skyReducerScalarsLoadedState s oracleVals)
              (v := .int (if s.focus < s.nodeCount then 1 else 0))]
            · exact skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals
            · simp [hfocus, isTruthy]
    _ = some (.returned (.int StepStatus.progress.code) (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
          exact execStmt_appTagPrefix_skyReducerScalarsLoaded_committed s oracleVals hwf hfocus happ

@[simp] theorem decodeKernelState?_restoreBlockState
    (maxNodes : Nat) (layout : ExecLayout) (before after : CState)
    (decls : List (String × CType)) :
    decodeKernelState? maxNodes layout (restoreBlockState before after decls) =
      decodeKernelState? maxNodes layout after := by
  have hHeap : (restoreBlockState before after decls).heap = after.heap := by
    induction decls generalizing after with
    | nil =>
        simp [restoreBlockState]
    | cons d ds ih =>
        rcases d with ⟨x, ty⟩
        cases hlookup : before.lookupVar x with
        | none =>
            calc
              (restoreBlockState before after ((x, ty) :: ds)).heap
                  = (restoreBlockState before (after.removeVar x) ds).heap := by
                      simp [restoreBlockState, hlookup]
              _ = (after.removeVar x).heap := ih (after := after.removeVar x)
              _ = after.heap := by
                  cases after
                  rfl
        | some v =>
            calc
              (restoreBlockState before after ((x, ty) :: ds)).heap
                  = (restoreBlockState before (after.updateVar x v) ds).heap := by
                      simp [restoreBlockState, hlookup]
              _ = (after.updateVar x v).heap := ih (after := after.updateVar x v)
              _ = after.heap := by
                  cases after
                  rfl
  simp [decodeKernelState?, hHeap]

theorem execStmt_commitAndReturn_halted_skyReducerScalarsLoaded
    (s : State) (oracleVals : Array Int) :
    execStmt 4 (SKYLowering.commitAndReturn .halted)
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerScalarsLoadedState s oracleVals)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
  exact execStmt_commitAndReturn_of_lookups .halted
    (skyReducerScalarsLoadedState s oracleVals)
    (layoutForState s oracleVals)
    (.int (Int.ofNat s.focus))
    (.int (Int.ofNat s.stack.length))
    (.int (Int.ofNat s.nodeCount))
    (skyReducerScalarsLoadedState_lookup_focusPtr s oracleVals)
    (skyReducerScalarsLoadedState_lookup_focus s oracleVals)
    (skyReducerScalarsLoadedState_lookup_stackSizePtr s oracleVals)
    (skyReducerScalarsLoadedState_lookup_stackSize s oracleVals)
    (skyReducerScalarsLoadedState_lookup_nodeCountPtr s oracleVals)
    (skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals)

theorem execStmt_invalidFocus_skyReducerEntry
    (s : State) (oracleVals : Array Int) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt 14
      (.seq
        (.assign (.var "focus") (.deref (.var "focusPtr")))
        (.seq
          (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))))
      (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerScalarsLoadedState s oracleVals)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
  calc
    execStmt 14
        (.seq
          (.assign (.var "focus") (.deref (.var "focusPtr")))
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted)))))
        (skyReducerEntry s oracleVals)
      = execStmt 13
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))))
          (skyReducerFocusLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 13
              (.assign (.var "focus") (.deref (.var "focusPtr")))
              (.seq
                (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                (.seq
                  (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                  (.ite
                    (.binop .lt (.var "focus") (.var "nodeCount"))
                    (.seq
                      (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                      (switchMany (.var "tag")
                        [ (NodeTag.code .app, SKYLowering.appCase)
                        , (NodeTag.code .combK, SKYLowering.kCase)
                        , (NodeTag.code .combS, SKYLowering.sCase)
                        , (NodeTag.code .combY, SKYLowering.yCase)
                        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                        (SKYLowering.commitAndReturn .halted)))
                    (SKYLowering.commitAndReturn .halted))))
              (skyReducerEntry s oracleVals)
              (skyReducerFocusLoadedState s oracleVals)
              (by simpa [execStmt, skyReducerFocusLoadedState] using
                execStmt_loadFocus_skyReducerEntry s oracleVals)
    _ = execStmt 12
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerStackSizeLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 12
              (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
              (.seq
                (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                (.ite
                  (.binop .lt (.var "focus") (.var "nodeCount"))
                  (.seq
                    (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                    (switchMany (.var "tag")
                      [ (NodeTag.code .app, SKYLowering.appCase)
                      , (NodeTag.code .combK, SKYLowering.kCase)
                      , (NodeTag.code .combS, SKYLowering.sCase)
                      , (NodeTag.code .combY, SKYLowering.yCase)
                      , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                      (SKYLowering.commitAndReturn .halted)))
                  (SKYLowering.commitAndReturn .halted)))
              (skyReducerFocusLoadedState s oracleVals)
              (skyReducerStackSizeLoadedState s oracleVals)
              (by simpa [execStmt] using
                execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals)
    _ = execStmt 11
          (.ite
            (.binop .lt (.var "focus") (.var "nodeCount"))
            (.seq
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted)))
            (SKYLowering.commitAndReturn .halted))
          (skyReducerScalarsLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 11
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))
              (skyReducerStackSizeLoadedState s oracleVals)
              (skyReducerScalarsLoadedState s oracleVals)
              (by simpa [execStmt] using
                execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals)
    _ = execStmt 10 (SKYLowering.commitAndReturn .halted)
          (skyReducerScalarsLoadedState s oracleVals) := by
            rw [execStmt_ite_of_eval_false
              (fuel := 10) (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
              (th := (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted))))
              (el := SKYLowering.commitAndReturn .halted)
              (st := skyReducerScalarsLoadedState s oracleVals)
              (v := .int (if s.focus < s.nodeCount then 1 else 0))]
            · exact skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals
            · simp [hfocus, isTruthy]
    _ = some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerScalarsLoadedState s oracleVals)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
            simpa using
              (execStmt_fuel_mono (extra := 6)
                (h := execStmt_commitAndReturn_halted_skyReducerScalarsLoaded s oracleVals))

theorem execStmt_invalidFocus_encodeExecState
    (s : State) (oracleVals : Array Int) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt 15 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerScalarsLoadedState s oracleVals)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 14
          (SKYLowering.seqs
            [ .assign (.var "focus") (.deref (.var "focusPtr"))
            , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
            , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
            , .ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted) ])
          (enterBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            [ ("tag", .int)
            , ("focus", .int)
            , ("stackSize", .int)
            , ("nodeCount", .int)
            , ("x", .int)
            , ("y", .int)
            , ("z", .int)
            , ("ref", .int) ]) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerScalarsLoadedState s oracleVals)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    simpa [SKYLowering.seqs, skyReducerEntry, skyReducerLocals] using
      (execStmt_invalidFocus_skyReducerEntry s oracleVals hfocus)
  rw [hbody]
  rfl

theorem execStmt_invalidFocus_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerScalarsLoadedState s oracleVals)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  simpa using
    (execStmt_fuel_mono (extra := 385)
      (h := execStmt_invalidFocus_encodeExecState s oracleVals hfocus))

theorem execStmt_appPath_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app) :
    execStmt 15 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerAppCommittedState s oracleVals hwf hfocus)
            skyReducerLocals)) := by
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 14
          (SKYLowering.seqs
            [ .assign (.var "focus") (.deref (.var "focusPtr"))
            , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
            , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
            , .ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted) ])
          (enterBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            [ ("tag", .int)
            , ("focus", .int)
            , ("stackSize", .int)
            , ("nodeCount", .int)
            , ("x", .int)
            , ("y", .int)
            , ("z", .int)
            , ("ref", .int) ]) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerAppCommittedState s oracleVals hwf hfocus)) := by
    simpa [SKYLowering.seqs, skyReducerEntry, skyReducerLocals] using
      (execStmt_appPath_skyReducerEntry s oracleVals hwf hfocus happ)
  rw [hbody]
  rfl

theorem execStmt_appPath_encodeExecState_fuel
    (extra : Nat) (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app) :
    execStmt (15 + extra) SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerAppCommittedState s oracleVals hwf hfocus)
            skyReducerLocals)) := by
  exact execStmt_fuel_mono
    (stmt := SKYLowering.skyReducerStepDecl.body)
    (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
    (res := .returned (.int StepStatus.progress.code)
      (restoreBlockState
        (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
        (skyReducerAppCommittedState s oracleVals hwf hfocus)
        skyReducerLocals))
    (extra := extra)
    (execStmt_appPath_encodeExecState s oracleVals hwf hfocus happ)

theorem execStmt_appPath_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerAppCommittedState s oracleVals hwf hfocus)
            skyReducerLocals)) := by
  simpa using execStmt_appPath_encodeExecState_fuel 385 s oracleVals hwf hfocus happ

theorem execStmt_tagSwitch_k_of_tagLoaded
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    execStmt 10
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        execStmt 8 SKYLowering.kCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
  simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
    skyReducerAppTagLoadedState, lookupVar_updateVar_eq, hk, NodeTag.code]

theorem skyReducerTagLoadedState_eval_stackTop
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (skyReducerKXVal s hstack) := by
  have hStackLookup :
      (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stack" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
    exact skyReducerAppTagLoadedState_lookup_stack s oracleVals hfocus
  have hStackSizeLookup :
      (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stackSize" =
        some (.int (Int.ofNat s.stack.length)) := by
    exact skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
  have hlenpos : 0 < s.stack.length := lt_of_lt_of_le (by decide : 0 < 2) hstack
  have hIdxLt : s.stack.length - 1 < s.stack.reverse.length := by
    simp
    omega
  have hTopIdx : s.stack.length - 1 - (s.stack.length - 1) < s.stack.length := by
    omega
  have hTop :
      s.stack.reverse.get ⟨s.stack.length - 1, hIdxLt⟩ =
        s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩ := by
    simpa using
      (List.get_reverse' (l := s.stack) (n := ⟨s.stack.length - 1, hIdxLt⟩) (hn' := hTopIdx))
  have hSub :
      evalExpr (SKYLowering.stackIx 1) (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.int (Int.ofNat (s.stack.length - 1))) := by
    have hlenge : 1 ≤ s.stack.length := by omega
    calc
      evalExpr (SKYLowering.stackIx 1) (skyReducerAppTagLoadedState s oracleVals hfocus)
        = some (.int (Int.ofNat s.stack.length - 1)) := by
            simp [SKYLowering.stackIx, evalExpr, evalStaticExpr, hStackSizeLookup]
      _ = some (.int (Int.ofNat (s.stack.length - 1))) := by
            simp [Int.ofNat_sub hlenge]
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase))
        (.int (Int.ofNat (s.stack.length - 1))) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑(s.stack.length - 1) := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑(s.stack.length - 1) then
        some (CVal.ptr 0
          (Int.ofNat (layoutForState s oracleVals).stackBase + Int.ofNat (s.stack.length - 1)))
      else none) =
        some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 1))))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerAppTagLoadedState s oracleVals hfocus).readPtr
        { block := 0
          offset := Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) } =
      (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) := by
    simpa using
      (CState.readPtr_block0
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1))
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)))
  have hHeapSame :
      (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) =
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) := by
    simp [skyReducerAppTagLoadedState, updateVar_heap]
  have hcell :
      readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) =
        some (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩) := by
    let h0 := writeIntList Heap.empty 0 s.tags.toList
    let h1 := writeNatList h0 s.maxNodes s.lhs.toList
    let h2 := writeNatList h1 (s.maxNodes + s.maxNodes) s.rhs.toList
    let h3 := writeNatList h2 (s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList
    let h4 := writeIntList h3 (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes)
      (oracleValuesPadded s oracleVals)
    let h5 := writeNatList h4
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals) s.stack.reverse
    let h6 := h5.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
      (.int (Int.ofNat s.focus))
    let h7 := h6.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
      (.int (Int.ofNat s.stack.length))
    let h8 := h7.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1)
      (.int (Int.ofNat s.nodeCount))
    have hcell' :
        readNatCell? h8
          (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 1)) =
            some (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩) := by
      simp only [h8, h7, h6]
      have haddrNeNodeCount :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 1) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeNodeCount]
      have haddrNeStackSize :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 1) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeStackSize]
      have haddrNeFocus :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 1) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeFocus]
      have hAt :
          readNatCell? h5
            (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length - 1)) =
            some (s.stack.reverse.get ⟨s.stack.length - 1, hIdxLt⟩) := by
        simpa [h5, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (readNatCell?_writeNatList_at
            (heap := h4)
            (base := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals)
            (xs := s.stack.reverse)
            (i := s.stack.length - 1)
            (by simpa using hIdxLt))
      calc
        readNatCell? h5
            (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length - 1))
          = some (s.stack.reverse.get ⟨s.stack.length - 1, hIdxLt⟩) := hAt
        _ = some (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩) := by
              simp [hTop]
    simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, encodeHeapWithLayout, encodeStackWithLayout,
      encodeOracleValuesWithLayout, encodeNodeArraysWithLayout, layoutForState, layoutFor]
      using hcell'
  have hHeap :
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) =
      some (.int (Int.ofNat (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩))) := by
    have hHeapEnc :
        (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) =
        some (.int (Int.ofNat (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩))) := by
      cases hread :
          (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
            ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) with
      | none =>
          simp [readNatCell?, readIntCell?, hread] at hcell
      | some v =>
          cases v with
          | int n =>
              simp [readNatCell?, readIntCell?, hread] at hcell
              have hn :
                  n = Int.ofNat (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩) := by
                calc
                  n = Int.ofNat n.toNat := by
                    symm
                    exact Int.toNat_of_nonneg hcell.1
                  _ = Int.ofNat (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩) := by
                    simp [hcell.2]
              simp [hread, hn]
          | ptr block offset =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | uint n sz =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | float v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | null =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | undef =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | structVal fields =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | unionVal tag v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
    simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
      skyReducerEntry, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
      encodeExecStateWithLayout, layoutForState, layoutFor] using hHeapEnc
  calc
    evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) := by
            simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hStackLookup, hSub, hAdd] using hReadPtr
    _ = (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) := hHeapSame
    _ = some (skyReducerKXVal s hstack) := by
          simp [skyReducerKXVal, hHeap]

theorem execStmt_kLoadX_tagLoaded
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt (fuel + 1)
      (.assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1)))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.normal (skyReducerKXLoadedState s oracleVals hfocus hstack)) := by
  have hEval := skyReducerTagLoadedState_eval_stackTop s oracleVals hfocus hstack
  simp [execStmt, skyReducerKXLoadedState, hEval]

theorem execStmt_kLoadFocus_afterLoadX
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt (fuel + 1) (.assign (.var "focus") (.var "x"))
      (skyReducerKXLoadedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerKFocusUpdatedState s oracleVals hfocus hstack)) := by
  have hX :
      (skyReducerKXLoadedState s oracleVals hfocus hstack).lookupVar "x" =
        some (skyReducerKXVal s hstack) := by
    rw [skyReducerKXLoadedState]
    simpa using
      lookupVar_updateVar_eq (skyReducerAppTagLoadedState s oracleVals hfocus) "x" (skyReducerKXVal s hstack)
  simp [execStmt, evalExpr, evalStaticExpr, skyReducerKFocusUpdatedState, hX]

theorem execStmt_kDecStackSize_afterFocus
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt (fuel + 1)
      (.assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2)))
      (skyReducerKFocusUpdatedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack)) := by
  have hlenge : 2 ≤ s.stack.length := hstack
  have hStackSize :
      (skyReducerKFocusUpdatedState s oracleVals hfocus hstack).lookupVar "stackSize" =
        some (.int (Int.ofNat s.stack.length)) := by
    rw [skyReducerKFocusUpdatedState]
    rw [lookupVar_updateVar_ne _ "focus" "stackSize" (skyReducerKXVal s hstack) (by decide)]
    rw [skyReducerKXLoadedState]
    rw [lookupVar_updateVar_ne _ "x" "stackSize" (skyReducerKXVal s hstack) (by decide)]
    exact skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
  have hSub :
      evalBinOp .sub (.int (Int.ofNat s.stack.length)) (.int 2) =
        some (.int (Int.ofNat s.stack.length - 2)) := by
    rfl
  simpa [execStmt, evalExpr, evalStaticExpr, skyReducerKStackSizeUpdatedState,
    hStackSize, hSub, Int.ofNat_sub hlenge]

theorem skyReducerKStackSizeUpdatedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "focus" =
      some (skyReducerKXVal s hstack) := by
  rw [skyReducerKStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focus" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerKFocusUpdatedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerKXLoadedState s oracleVals hfocus hstack) "focus" (skyReducerKXVal s hstack)

theorem skyReducerKStackSizeUpdatedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "stackSize" =
      some (.int (Int.ofNat (s.stack.length - 2))) := by
  rw [skyReducerKStackSizeUpdatedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerKFocusUpdatedState s oracleVals hfocus hstack)
      "stackSize" (.int (Int.ofNat (s.stack.length - 2)))

theorem skyReducerKStackSizeUpdatedState_lookup_focusPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  rw [skyReducerKStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focusPtr" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerKFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "focusPtr" (skyReducerKXVal s hstack) (by decide)]
  rw [skyReducerKXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "focusPtr" (skyReducerKXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "focusPtr" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "focusPtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focusPtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "focusPtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_focusPtr s oracleVals

theorem skyReducerKStackSizeUpdatedState_lookup_stackSizePtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  rw [skyReducerKStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stackSizePtr" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerKFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "stackSizePtr" (skyReducerKXVal s hstack) (by decide)]
  rw [skyReducerKXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "stackSizePtr" (skyReducerKXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "stackSizePtr" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "stackSizePtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stackSizePtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "stackSizePtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_stackSizePtr s oracleVals

theorem skyReducerKStackSizeUpdatedState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  rw [skyReducerKStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCountPtr" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerKFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCountPtr" (skyReducerKXVal s hstack) (by decide)]
  rw [skyReducerKXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "nodeCountPtr" (skyReducerKXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "nodeCountPtr" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "nodeCountPtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCountPtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCountPtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_nodeCountPtr s oracleVals

theorem skyReducerKStackSizeUpdatedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerKStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCount" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerKFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCount" (skyReducerKXVal s hstack) (by decide)]
  rw [skyReducerKXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "nodeCount" (skyReducerKXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "nodeCount" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  exact skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals

theorem execStmt_kWriteFocusPtr_afterStackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt 2 (SKYLowering.writeScalar "focusPtr" (.var "focus"))
      (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerKCommittedFocusState s oracleVals hfocus hstack)) := by
  simpa [skyReducerKCommittedFocusState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack) "focusPtr" "focus"
      (layoutForState s oracleVals).focusBase (skyReducerKXVal s hstack)
      (skyReducerKStackSizeUpdatedState_lookup_focusPtr s oracleVals hfocus hstack)
      (skyReducerKStackSizeUpdatedState_lookup_focus s oracleVals hfocus hstack))

theorem execStmt_kWriteStackSizePtr_afterFocusPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt 2 (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
      (skyReducerKCommittedFocusState s oracleVals hfocus hstack) =
        some (.normal (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack)) := by
  have hPtr :
      (skyReducerKCommittedFocusState s oracleVals hfocus hstack).lookupVar "stackSizePtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
    simpa [skyReducerKCommittedFocusState] using
      (skyReducerKStackSizeUpdatedState_lookup_stackSizePtr s oracleVals hfocus hstack)
  have hVal :
      (skyReducerKCommittedFocusState s oracleVals hfocus hstack).lookupVar "stackSize" =
        some (.int (Int.ofNat (s.stack.length - 2))) := by
    simpa [skyReducerKCommittedFocusState] using
      (skyReducerKStackSizeUpdatedState_lookup_stackSize s oracleVals hfocus hstack)
  simpa [skyReducerKCommittedStackSizeState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerKCommittedFocusState s oracleVals hfocus hstack) "stackSizePtr" "stackSize"
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))
      hPtr hVal)

theorem execStmt_kWriteNodeCountPtr_afterStackSizePtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt 2 (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
      (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack) =
        some (.normal (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
  have hPtr :
      (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).lookupVar "nodeCountPtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
    simpa [skyReducerKCommittedStackSizeState, skyReducerKCommittedFocusState] using
      (skyReducerKStackSizeUpdatedState_lookup_nodeCountPtr s oracleVals hfocus hstack)
  have hVal :
      (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerKCommittedStackSizeState, skyReducerKCommittedFocusState] using
      (skyReducerKStackSizeUpdatedState_lookup_nodeCount s oracleVals hfocus hstack)
  simpa [skyReducerKCommittedState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack) "nodeCountPtr" "nodeCount"
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))
      hPtr hVal)

theorem execStmt_kCommit_afterStackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt 4 (SKYLowering.commitAndReturn .progress)
      (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack) =
        some (.returned (.int StepStatus.progress.code) (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
  exact execStmt_commitAndReturn_of_steps .progress
    (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack)
    (skyReducerKCommittedFocusState s oracleVals hfocus hstack)
    (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack)
    (skyReducerKCommittedState s oracleVals hfocus hstack)
    (execStmt_kWriteFocusPtr_afterStackSize s oracleVals hfocus hstack)
    (execStmt_kWriteStackSizePtr_afterFocusPtr s oracleVals hfocus hstack)
    (execStmt_kWriteNodeCountPtr_afterStackSizePtr s oracleVals hfocus hstack)

theorem execStmt_kCase_tagLoaded
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt 8 SKYLowering.kCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.progress.code) (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
  have hGuard :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 2)) (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.int 1) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hge : (2 : Int) ≤ (s.stack.length : Int) := by
      exact_mod_cast hstack
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 2)) (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 2) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 2 then 1 else 0)) := by
            rfl
      _ = some (.int 1) := by
            simp [hge]
  calc
    execStmt 8 SKYLowering.kCase (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 7
          (SKYLowering.seqs
            [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
            , .assign (.var "focus") (.var "x")
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.kCase, SKYLowering.seqs] using
              (execStmt_ite_of_eval_true
                (fuel := 7)
                (cond := (.binop .ge (.var "stackSize") (.intLit 2)))
                (th := SKYLowering.seqs
                  [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                  , .assign (.var "focus") (.var "x")
                  , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                  , SKYLowering.commitAndReturn .progress ])
                (el := SKYLowering.commitAndReturn .halted)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 1)
                hGuard
                (by simp [isTruthy]))
    _ = execStmt 6
          (SKYLowering.seqs
            [ .assign (.var "focus") (.var "x")
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerKXLoadedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 6
              (.assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1)))
              (SKYLowering.seqs
                [ .assign (.var "focus") (.var "x")
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (skyReducerKXLoadedState s oracleVals hfocus hstack)
              (execStmt_kLoadX_tagLoaded 6 s oracleVals hfocus hstack)
    _ = execStmt 5
          (SKYLowering.seqs
            [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerKFocusUpdatedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 5
              (.assign (.var "focus") (.var "x"))
              (SKYLowering.seqs
                [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerKXLoadedState s oracleVals hfocus hstack)
              (skyReducerKFocusUpdatedState s oracleVals hfocus hstack)
              (execStmt_kLoadFocus_afterLoadX 5 s oracleVals hfocus hstack)
    _ = execStmt 4 (SKYLowering.commitAndReturn .progress)
          (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 4
              (.assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2)))
              (SKYLowering.commitAndReturn .progress)
              (skyReducerKFocusUpdatedState s oracleVals hfocus hstack)
              (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack)
              (execStmt_kDecStackSize_afterFocus 4 s oracleVals hfocus hstack)
    _ = some (.returned (.int StepStatus.progress.code) (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
          exact execStmt_kCommit_afterStackSize s oracleVals hfocus hstack

theorem execStmt_tagSwitch_k_of_tagLoaded_committed
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    execStmt 10
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.progress.code) (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
  calc
    execStmt 10
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted))
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 8 SKYLowering.kCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
          exact execStmt_tagSwitch_k_of_tagLoaded s oracleVals hfocus hk
    _ = some (.returned (.int StepStatus.progress.code) (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
          exact execStmt_kCase_tagLoaded s oracleVals hfocus hstack

theorem execStmt_kTagPrefix_skyReducerScalarsLoaded_committed
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    execStmt 11
      (.seq
        (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted)))
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.progress.code) (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
  calc
    execStmt 11
        (.seq
          (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted)))
        (skyReducerScalarsLoadedState s oracleVals)
      = execStmt 10
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            exact execStmt_seq_of_normal 10
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted))
              (skyReducerScalarsLoadedState s oracleVals)
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (by
                simpa [execStmt, skyReducerAppTagLoadedState] using
                  execStmt_loadTag_skyReducerScalarsLoaded s oracleVals hwf hfocus)
    _ = some (.returned (.int StepStatus.progress.code) (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
          exact execStmt_tagSwitch_k_of_tagLoaded_committed s oracleVals hfocus hstack hk

theorem execStmt_kPath_skyReducerEntry
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    execStmt 15
      (.seq
        (.assign (.var "focus") (.deref (.var "focusPtr")))
        (.seq
          (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))))
      (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.progress.code) (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
  calc
    execStmt 15
        (.seq
          (.assign (.var "focus") (.deref (.var "focusPtr")))
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted)))))
        (skyReducerEntry s oracleVals)
      = execStmt 14
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))))
          (skyReducerFocusLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 14
              (.assign (.var "focus") (.deref (.var "focusPtr")))
              (.seq
                (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                (.seq
                  (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                  (.ite
                    (.binop .lt (.var "focus") (.var "nodeCount"))
                    (.seq
                      (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                      (switchMany (.var "tag")
                        [ (NodeTag.code .app, SKYLowering.appCase)
                        , (NodeTag.code .combK, SKYLowering.kCase)
                        , (NodeTag.code .combS, SKYLowering.sCase)
                        , (NodeTag.code .combY, SKYLowering.yCase)
                        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                        (SKYLowering.commitAndReturn .halted)))
                    (SKYLowering.commitAndReturn .halted))))
              (skyReducerEntry s oracleVals)
              (skyReducerFocusLoadedState s oracleVals)
              (by simpa [execStmt, skyReducerFocusLoadedState] using execStmt_loadFocus_skyReducerEntry s oracleVals)
    _ = execStmt 13
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerStackSizeLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 13
              (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
              (.seq
                (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                (.ite
                  (.binop .lt (.var "focus") (.var "nodeCount"))
                  (.seq
                    (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                    (switchMany (.var "tag")
                      [ (NodeTag.code .app, SKYLowering.appCase)
                      , (NodeTag.code .combK, SKYLowering.kCase)
                      , (NodeTag.code .combS, SKYLowering.sCase)
                      , (NodeTag.code .combY, SKYLowering.yCase)
                      , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                      (SKYLowering.commitAndReturn .halted)))
                  (SKYLowering.commitAndReturn .halted)))
              (skyReducerFocusLoadedState s oracleVals)
              (skyReducerStackSizeLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals)
    _ = execStmt 12
          (.ite
            (.binop .lt (.var "focus") (.var "nodeCount"))
            (.seq
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted)))
            (SKYLowering.commitAndReturn .halted))
          (skyReducerScalarsLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 12
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))
              (skyReducerStackSizeLoadedState s oracleVals)
              (skyReducerScalarsLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals)
    _ = execStmt 11
          (.seq
            (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
            (switchMany (.var "tag")
              [ (NodeTag.code .app, SKYLowering.appCase)
              , (NodeTag.code .combK, SKYLowering.kCase)
              , (NodeTag.code .combS, SKYLowering.sCase)
              , (NodeTag.code .combY, SKYLowering.yCase)
              , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerScalarsLoadedState s oracleVals) := by
            rw [execStmt_ite_of_eval_true
              (fuel := 11) (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
              (th := (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted))))
              (el := SKYLowering.commitAndReturn .halted)
              (st := skyReducerScalarsLoadedState s oracleVals)
              (v := .int (if s.focus < s.nodeCount then 1 else 0))]
            · exact skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals
            · simp [hfocus, isTruthy]
    _ = some (.returned (.int StepStatus.progress.code) (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
          exact execStmt_kTagPrefix_skyReducerScalarsLoaded_committed s oracleVals hwf hfocus hstack hk

theorem execStmt_kPath_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    execStmt 16 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerKCommittedState s oracleVals hfocus hstack)
            skyReducerLocals)) := by
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 15
          (SKYLowering.seqs
            [ .assign (.var "focus") (.deref (.var "focusPtr"))
            , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
            , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
            , .ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted) ])
          (enterBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            [ ("tag", .int)
            , ("focus", .int)
            , ("stackSize", .int)
            , ("nodeCount", .int)
            , ("x", .int)
            , ("y", .int)
            , ("z", .int)
            , ("ref", .int) ]) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerKCommittedState s oracleVals hfocus hstack)) := by
    simpa [SKYLowering.seqs, skyReducerEntry, skyReducerLocals] using
      (execStmt_kPath_skyReducerEntry s oracleVals hwf hfocus hstack hk)
  rw [hbody]
  rfl

theorem execStmt_kPath_encodeExecState_fuel
    (extra : Nat) (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length)
    (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    execStmt (16 + extra) SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerKCommittedState s oracleVals hfocus hstack)
            skyReducerLocals)) := by
  exact execStmt_fuel_mono
    (h := execStmt_kPath_encodeExecState s oracleVals hwf hfocus hstack hk)

theorem execStmt_kPath_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length)
    (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerKCommittedState s oracleVals hfocus hstack)
            skyReducerLocals)) := by
  simpa using execStmt_kPath_encodeExecState_fuel 384 s oracleVals hwf hfocus hstack hk

theorem skyReducerTagLoadedState_eval_stackTop1
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (skyReducerYXVal s hstack) := by
  have hStackLookup :
      (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stack" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
    exact skyReducerAppTagLoadedState_lookup_stack s oracleVals hfocus
  have hStackSizeLookup :
      (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stackSize" =
        some (.int (Int.ofNat s.stack.length)) := by
    exact skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
  have hIdxLt : s.stack.length - 1 < s.stack.reverse.length := by
    simp
    omega
  have hTopIdx : s.stack.length - 1 - (s.stack.length - 1) < s.stack.length := by
    omega
  have hTop :
      s.stack.reverse.get ⟨s.stack.length - 1, hIdxLt⟩ =
        s.stack.get ⟨0, by omega⟩ := by
    simpa using
      (List.get_reverse' (l := s.stack) (n := ⟨s.stack.length - 1, hIdxLt⟩) (hn' := hTopIdx))
  have hSub :
      evalExpr (SKYLowering.stackIx 1) (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.int (Int.ofNat (s.stack.length - 1))) := by
    calc
      evalExpr (SKYLowering.stackIx 1) (skyReducerAppTagLoadedState s oracleVals hfocus)
        = some (.int (Int.ofNat s.stack.length - 1)) := by
            simp [SKYLowering.stackIx, evalExpr, evalStaticExpr, hStackSizeLookup]
      _ = some (.int (Int.ofNat (s.stack.length - 1))) := by
            simp [Int.ofNat_sub hstack]
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase))
        (.int (Int.ofNat (s.stack.length - 1))) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑(s.stack.length - 1) := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑(s.stack.length - 1) then
        some (CVal.ptr 0
          (Int.ofNat (layoutForState s oracleVals).stackBase + Int.ofNat (s.stack.length - 1)))
      else none) =
        some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 1))))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerAppTagLoadedState s oracleVals hfocus).readPtr
        { block := 0
          offset := Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) } =
      (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) := by
    simpa using
      (CState.readPtr_block0
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1))
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)))
  have hHeapSame :
      (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) =
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) := by
    simp [skyReducerAppTagLoadedState, updateVar_heap]
  have hcell :
      readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) =
        some (s.stack.get ⟨0, by omega⟩) := by
    let h0 := writeIntList Heap.empty 0 s.tags.toList
    let h1 := writeNatList h0 s.maxNodes s.lhs.toList
    let h2 := writeNatList h1 (s.maxNodes + s.maxNodes) s.rhs.toList
    let h3 := writeNatList h2 (s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList
    let h4 := writeIntList h3 (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes)
      (oracleValuesPadded s oracleVals)
    let h5 := writeNatList h4
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals) s.stack.reverse
    let h6 := h5.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
      (.int (Int.ofNat s.focus))
    let h7 := h6.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
      (.int (Int.ofNat s.stack.length))
    let h8 := h7.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1)
      (.int (Int.ofNat s.nodeCount))
    have hcell' :
        readNatCell? h8
          (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 1)) =
            some (s.stack.get ⟨0, by omega⟩) := by
      simp only [h8, h7, h6]
      have haddrNeNodeCount :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 1) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeNodeCount]
      have haddrNeStackSize :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 1) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeStackSize]
      have haddrNeFocus :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 1) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeFocus]
      have hAt :
          readNatCell? h5
            (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length - 1)) =
            some (s.stack.reverse.get ⟨s.stack.length - 1, hIdxLt⟩) := by
        simpa [h5, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (readNatCell?_writeNatList_at
            (heap := h4)
            (base := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals)
            (xs := s.stack.reverse)
            (i := s.stack.length - 1)
            (by simpa using hIdxLt))
      calc
        readNatCell? h5
            (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length - 1))
          = some (s.stack.reverse.get ⟨s.stack.length - 1, hIdxLt⟩) := hAt
        _ = some (s.stack.get ⟨0, by omega⟩) := by
              simp [hTop]
    simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, encodeHeapWithLayout, encodeStackWithLayout,
      encodeOracleValuesWithLayout, encodeNodeArraysWithLayout, layoutForState, layoutFor]
      using hcell'
  have hHeap :
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) =
      some (.int (Int.ofNat (s.stack.get ⟨0, by omega⟩))) := by
    have hHeapEnc :
        (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) =
        some (.int (Int.ofNat (s.stack.get ⟨0, by omega⟩))) := by
      cases hread :
          (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
            ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) with
      | none =>
          simp [readNatCell?, readIntCell?, hread] at hcell
      | some v =>
          cases v with
          | int n =>
              simp [readNatCell?, readIntCell?, hread] at hcell
              have hn : n = Int.ofNat (s.stack.get ⟨0, by omega⟩) := by
                calc
                  n = Int.ofNat n.toNat := by
                    symm
                    exact Int.toNat_of_nonneg hcell.1
                  _ = Int.ofNat (s.stack.get ⟨0, by omega⟩) := by
                    simp [hcell.2]
              simp [hread, hn]
          | ptr block offset =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | uint n sz =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | float v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | null =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | undef =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | structVal fields =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | unionVal tag v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
    simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
      skyReducerEntry, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
      encodeExecStateWithLayout, layoutForState, layoutFor] using hHeapEnc
  calc
    evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) := by
            simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hStackLookup, hSub, hAdd] using hReadPtr
    _ = (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 1)) := hHeapSame
    _ = some (skyReducerYXVal s hstack) := by
          simp [skyReducerYXVal, hHeap]

theorem skyReducerYXLoadedState_lookup_x
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYXLoadedState s oracleVals hfocus hstack).lookupVar "x" =
      some (skyReducerYXVal s hstack) := by
  rw [skyReducerYXLoadedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerAppTagLoadedState s oracleVals hfocus) "x" (skyReducerYXVal s hstack)

theorem skyReducerYXLoadedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYXLoadedState s oracleVals hfocus hstack).lookupVar "focus" =
      some (.int (Int.ofNat s.focus)) := by
  rw [skyReducerYXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "focus"
      (skyReducerYXVal s hstack) (by decide : "focus" ≠ "x"))

theorem skyReducerYXLoadedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYXLoadedState s oracleVals hfocus hstack).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerYXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "stackSize"
      (skyReducerYXVal s hstack) (by decide : "stackSize" ≠ "x"))

theorem skyReducerYXLoadedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYXLoadedState s oracleVals hfocus hstack).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerYXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "nodeCount" (skyReducerYXVal s hstack) (by decide)]
  exact skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals

theorem skyReducerYXLoadedState_lookup_tags
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYXLoadedState s oracleVals hfocus hstack).lookupVar "tags" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).tagsBase)) := by
  rw [skyReducerYXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "tags"
      (skyReducerYXVal s hstack) (by decide : "tags" ≠ "x"))

theorem skyReducerYXLoadedState_lookup_lhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYXLoadedState s oracleVals hfocus hstack).lookupVar "lhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
  rw [skyReducerYXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "lhs"
      (skyReducerYXVal s hstack) (by decide : "lhs" ≠ "x"))

theorem skyReducerYXLoadedState_lookup_rhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYXLoadedState s oracleVals hfocus hstack).lookupVar "rhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
  rw [skyReducerYXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "rhs"
      (skyReducerYXVal s hstack) (by decide : "rhs" ≠ "x"))

theorem skyReducerYXLoadedState_lookup_oracleRefs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYXLoadedState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
  rw [skyReducerYXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "oracleRefs"
      (skyReducerYXVal s hstack) (by decide : "oracleRefs" ≠ "x"))

theorem execStmt_yLoadX_tagLoaded
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt (fuel + 1)
      (.assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1)))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.normal (skyReducerYXLoadedState s oracleVals hfocus hstack)) := by
  have hEval := skyReducerTagLoadedState_eval_stackTop1 s oracleVals hfocus hstack
  simp [execStmt, skyReducerYXLoadedState, hEval]

theorem execStmt_yStoreSelfTag_afterLoadX
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr)
      (skyReducerYXLoadedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYSelfTagStoredState s oracleVals hfocus hstack)) := by
  have hBase := skyReducerYXLoadedState_lookup_tags s oracleVals hfocus hstack
  have hNodeCount := skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack
  have hAddr :
      evalExpr (.binop .add (.var "tags") (SKYLowering.nodeIx 0))
        (skyReducerYXLoadedState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).tagsBase + s.nodeCount))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerYXLoadedState s oracleVals hfocus hstack)
        (baseName := "tags")
        (base := (layoutForState s oracleVals).tagsBase)
        (nodeCount := s.nodeCount)
        (offset := 0)
        hBase hNodeCount)
  have hVal :
      evalExpr SKYLowering.appTagExpr (skyReducerYXLoadedState s oracleVals hfocus hstack) =
        some (.int (NodeTag.code .app)) := by
    simp [SKYLowering.appTagExpr, evalExpr, evalStaticExpr]
  simpa [skyReducerYSelfTagStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerYXLoadedState s oracleVals hfocus hstack)
      (base := "tags") (idx := SKYLowering.nodeIx 0) (value := SKYLowering.appTagExpr)
      (addr := (layoutForState s oracleVals).tagsBase + s.nodeCount)
      (v := .int (NodeTag.code .app)) hAddr hVal)

theorem execStmt_yStoreSelfLhs_afterSelfTag
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus"))
      (skyReducerYSelfTagStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).lookupVar "lhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
    simpa [skyReducerYSelfTagStoredState] using
      (skyReducerYXLoadedState_lookup_lhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerYSelfTagStoredState] using
      (skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "lhs") (SKYLowering.nodeIx 0))
        (skyReducerYSelfTagStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.nodeCount))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerYSelfTagStoredState s oracleVals hfocus hstack)
        (baseName := "lhs")
        (base := (layoutForState s oracleVals).lhsBase)
        (nodeCount := s.nodeCount)
        (offset := 0)
        hBase hNodeCount)
  have hFocus :
      (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).lookupVar "focus" =
        some (.int (Int.ofNat s.focus)) := by
    simpa [skyReducerYSelfTagStoredState] using
      (skyReducerYXLoadedState_lookup_focus s oracleVals hfocus hstack)
  have hVal : evalExpr (.var "focus") (skyReducerYSelfTagStoredState s oracleVals hfocus hstack) =
      some (.int (Int.ofNat s.focus)) := by
    simp [evalExpr, evalStaticExpr, hFocus]
  simpa [skyReducerYSelfLhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerYSelfTagStoredState s oracleVals hfocus hstack)
      (base := "lhs") (idx := SKYLowering.nodeIx 0) (value := (.var "focus"))
      (addr := (layoutForState s oracleVals).lhsBase + s.nodeCount)
      (v := .int (Int.ofNat s.focus)) hAddr hVal)

theorem execStmt_yStoreSelfRhs_afterSelfLhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x"))
      (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).lookupVar "rhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
    simpa [skyReducerYSelfLhsStoredState] using
      (skyReducerYXLoadedState_lookup_rhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerYSelfLhsStoredState] using
      (skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "rhs") (SKYLowering.nodeIx 0))
        (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).rhsBase + s.nodeCount))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerYSelfLhsStoredState s oracleVals hfocus hstack)
        (baseName := "rhs")
        (base := (layoutForState s oracleVals).rhsBase)
        (nodeCount := s.nodeCount)
        (offset := 0)
        hBase hNodeCount)
  have hX :
      (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).lookupVar "x" =
        some (skyReducerYXVal s hstack) := by
    simpa [skyReducerYSelfLhsStoredState] using
      (skyReducerYXLoadedState_lookup_x s oracleVals hfocus hstack)
  have hVal : evalExpr (.var "x") (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack) =
      some (skyReducerYXVal s hstack) := by
    simp [evalExpr, evalStaticExpr, hX]
  simpa [skyReducerYSelfRhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerYSelfLhsStoredState s oracleVals hfocus hstack)
      (base := "rhs") (idx := SKYLowering.nodeIx 0) (value := (.var "x"))
      (addr := (layoutForState s oracleVals).rhsBase + s.nodeCount)
      (v := skyReducerYXVal s hstack) hAddr hVal)

theorem execStmt_yStoreSelfRef_afterSelfRhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0))
      (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYSelfRefStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
    simpa [skyReducerYSelfRhsStoredState] using
      (skyReducerYXLoadedState_lookup_oracleRefs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerYSelfRhsStoredState] using
      (skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "oracleRefs") (SKYLowering.nodeIx 0))
        (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).refsBase + s.nodeCount))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerYSelfRhsStoredState s oracleVals hfocus hstack)
        (baseName := "oracleRefs")
        (base := (layoutForState s oracleVals).refsBase)
        (nodeCount := s.nodeCount)
        (offset := 0)
        hBase hNodeCount)
  have hVal : evalExpr (.intLit 0) (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack) =
      some (.int 0) := by
    simp [evalExpr, evalStaticExpr]
  simpa [skyReducerYSelfRefStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerYSelfRhsStoredState s oracleVals hfocus hstack)
      (base := "oracleRefs") (idx := SKYLowering.nodeIx 0) (value := (.intLit 0))
      (addr := (layoutForState s oracleVals).refsBase + s.nodeCount)
      (v := .int 0) hAddr hVal)

theorem execStmt_yStoreOutTag_afterSelfRef
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr)
      (skyReducerYSelfRefStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYOutTagStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).lookupVar "tags" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).tagsBase)) := by
    simpa [skyReducerYSelfRefStoredState] using
      (skyReducerYXLoadedState_lookup_tags s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerYSelfRefStoredState] using
      (skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "tags") (SKYLowering.nodeIx 1))
        (skyReducerYSelfRefStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).tagsBase + s.nodeCount + 1))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerYSelfRefStoredState s oracleVals hfocus hstack)
        (baseName := "tags")
        (base := (layoutForState s oracleVals).tagsBase)
        (nodeCount := s.nodeCount)
        (offset := 1)
        hBase hNodeCount)
  have hVal :
      evalExpr SKYLowering.appTagExpr (skyReducerYSelfRefStoredState s oracleVals hfocus hstack) =
        some (.int (NodeTag.code .app)) := by
    simp [SKYLowering.appTagExpr, evalExpr, evalStaticExpr]
  simpa [skyReducerYOutTagStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerYSelfRefStoredState s oracleVals hfocus hstack)
      (base := "tags") (idx := SKYLowering.nodeIx 1) (value := SKYLowering.appTagExpr)
      (addr := (layoutForState s oracleVals).tagsBase + s.nodeCount + 1)
      (v := .int (NodeTag.code .app)) hAddr hVal)

theorem execStmt_yStoreOutLhs_afterOutTag
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x"))
      (skyReducerYOutTagStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYOutLhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerYOutTagStoredState s oracleVals hfocus hstack).lookupVar "lhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
    simpa [skyReducerYOutTagStoredState] using
      (skyReducerYXLoadedState_lookup_lhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerYOutTagStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerYOutTagStoredState] using
      (skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "lhs") (SKYLowering.nodeIx 1))
        (skyReducerYOutTagStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.nodeCount + 1))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerYOutTagStoredState s oracleVals hfocus hstack)
        (baseName := "lhs")
        (base := (layoutForState s oracleVals).lhsBase)
        (nodeCount := s.nodeCount)
        (offset := 1)
        hBase hNodeCount)
  have hX :
      (skyReducerYOutTagStoredState s oracleVals hfocus hstack).lookupVar "x" =
        some (skyReducerYXVal s hstack) := by
    simpa [skyReducerYOutTagStoredState] using
      (skyReducerYXLoadedState_lookup_x s oracleVals hfocus hstack)
  have hVal : evalExpr (.var "x") (skyReducerYOutTagStoredState s oracleVals hfocus hstack) =
      some (skyReducerYXVal s hstack) := by
    simp [evalExpr, evalStaticExpr, hX]
  simpa [skyReducerYOutLhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerYOutTagStoredState s oracleVals hfocus hstack)
      (base := "lhs") (idx := SKYLowering.nodeIx 1) (value := (.var "x"))
      (addr := (layoutForState s oracleVals).lhsBase + s.nodeCount + 1)
      (v := skyReducerYXVal s hstack) hAddr hVal)

theorem execStmt_yStoreOutRhs_afterOutLhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0))
      (skyReducerYOutLhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYOutRhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerYOutLhsStoredState s oracleVals hfocus hstack).lookupVar "rhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
    simpa [skyReducerYOutLhsStoredState] using
      (skyReducerYXLoadedState_lookup_rhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerYOutLhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerYOutLhsStoredState] using
      (skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "rhs") (SKYLowering.nodeIx 1))
        (skyReducerYOutLhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).rhsBase + s.nodeCount + 1))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerYOutLhsStoredState s oracleVals hfocus hstack)
        (baseName := "rhs")
        (base := (layoutForState s oracleVals).rhsBase)
        (nodeCount := s.nodeCount)
        (offset := 1)
        hBase hNodeCount)
  have hVal : evalExpr (SKYLowering.nodeIx 0) (skyReducerYOutLhsStoredState s oracleVals hfocus hstack) =
      some (skyReducerYSelfVal s) := by
    simpa [skyReducerYSelfVal] using
      (evalExpr_nodeIx_of_lookup (st := skyReducerYOutLhsStoredState s oracleVals hfocus hstack)
        (nodeCount := s.nodeCount) (offset := 0) hNodeCount)
  simpa [skyReducerYOutRhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerYOutLhsStoredState s oracleVals hfocus hstack)
      (base := "rhs") (idx := SKYLowering.nodeIx 1) (value := SKYLowering.nodeIx 0)
      (addr := (layoutForState s oracleVals).rhsBase + s.nodeCount + 1)
      (v := skyReducerYSelfVal s) hAddr hVal)

theorem execStmt_yStoreOutRef_afterOutRhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0))
      (skyReducerYOutRhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYOutRefStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerYOutRhsStoredState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
    simpa [skyReducerYOutRhsStoredState] using
      (skyReducerYXLoadedState_lookup_oracleRefs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerYOutRhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerYOutRhsStoredState] using
      (skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "oracleRefs") (SKYLowering.nodeIx 1))
        (skyReducerYOutRhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).refsBase + s.nodeCount + 1))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerYOutRhsStoredState s oracleVals hfocus hstack)
        (baseName := "oracleRefs")
        (base := (layoutForState s oracleVals).refsBase)
        (nodeCount := s.nodeCount)
        (offset := 1)
        hBase hNodeCount)
  have hVal : evalExpr (.intLit 0) (skyReducerYOutRhsStoredState s oracleVals hfocus hstack) =
      some (.int 0) := by
    simp [evalExpr, evalStaticExpr]
  simpa [skyReducerYOutRefStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerYOutRhsStoredState s oracleVals hfocus hstack)
      (base := "oracleRefs") (idx := SKYLowering.nodeIx 1) (value := (.intLit 0))
      (addr := (layoutForState s oracleVals).refsBase + s.nodeCount + 1)
      (v := .int 0) hAddr hVal)

theorem execStmt_ySetFocus_afterStores
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2 (.assign (.var "focus") (SKYLowering.nodeIx 1))
      (skyReducerYOutRefStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYFocusUpdatedState s oracleVals hfocus hstack)) := by
  have hNodeCount :
      (skyReducerYOutRefStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerYOutRefStoredState] using
      (skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hEval : evalExpr (SKYLowering.nodeIx 1) (skyReducerYOutRefStoredState s oracleVals hfocus hstack) =
      some (skyReducerYOutVal s) := by
    simpa [skyReducerYOutVal] using
      (evalExpr_nodeIx_of_lookup (st := skyReducerYOutRefStoredState s oracleVals hfocus hstack)
        (nodeCount := s.nodeCount) (offset := 1) hNodeCount)
  simp [execStmt, skyReducerYFocusUpdatedState, hEval]

theorem execStmt_yIncNodeCount_afterFocus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2 (.assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2)))
      (skyReducerYFocusUpdatedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYNodeCountUpdatedState s oracleVals hfocus hstack)) := by
  have hNodeCount :
      (skyReducerYFocusUpdatedState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    rw [skyReducerYFocusUpdatedState]
    rw [lookupVar_updateVar_ne _ "focus" "nodeCount" (skyReducerYOutVal s) (by decide)]
    simpa [skyReducerYOutRefStoredState] using
      (skyReducerYXLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hEval :
      evalExpr (.binop .add (.var "nodeCount") (.intLit 2))
        (skyReducerYFocusUpdatedState s oracleVals hfocus hstack) =
          some (.int (Int.ofNat (s.nodeCount + 2))) := by
    simp [evalExpr, evalStaticExpr, hNodeCount, Int.ofNat_add]
  simp [execStmt, skyReducerYNodeCountUpdatedState, hEval]

theorem execStmt_yDecStackSize_afterNodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2 (.assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1)))
      (skyReducerYNodeCountUpdatedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack)) := by
  have hStackSize :
      (skyReducerYNodeCountUpdatedState s oracleVals hfocus hstack).lookupVar "stackSize" =
        some (.int (Int.ofNat s.stack.length)) := by
    rw [skyReducerYNodeCountUpdatedState]
    rw [lookupVar_updateVar_ne _ "nodeCount" "stackSize" (.int (Int.ofNat (s.nodeCount + 2))) (by decide)]
    rw [skyReducerYFocusUpdatedState]
    rw [lookupVar_updateVar_ne _ "focus" "stackSize" (skyReducerYOutVal s) (by decide)]
    simpa [skyReducerYOutRefStoredState] using
      (skyReducerYXLoadedState_lookup_stackSize s oracleVals hfocus hstack)
  have hEval :
      evalExpr (.binop .sub (.var "stackSize") (.intLit 1))
        (skyReducerYNodeCountUpdatedState s oracleVals hfocus hstack) =
          some (.int (Int.ofNat (s.stack.length - 1))) := by
    simp [evalExpr, evalStaticExpr, hStackSize, Int.ofNat_sub hstack]
  simp [execStmt, skyReducerYStackSizeUpdatedState, hEval]

theorem skyReducerYStackSizeUpdatedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "focus" =
      some (skyReducerYOutVal s) := by
  rw [skyReducerYStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focus" (.int (Int.ofNat (s.stack.length - 1))) (by decide)]
  rw [skyReducerYNodeCountUpdatedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "focus" (.int (Int.ofNat (s.nodeCount + 2))) (by decide)]
  rw [skyReducerYFocusUpdatedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerYOutRefStoredState s oracleVals hfocus hstack) "focus" (skyReducerYOutVal s)

theorem skyReducerYStackSizeUpdatedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "stackSize" =
      some (.int (Int.ofNat (s.stack.length - 1))) := by
  rw [skyReducerYStackSizeUpdatedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerYNodeCountUpdatedState s oracleVals hfocus hstack)
      "stackSize" (.int (Int.ofNat (s.stack.length - 1)))

theorem skyReducerYStackSizeUpdatedState_lookup_focusPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  rw [skyReducerYStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focusPtr" (.int (Int.ofNat (s.stack.length - 1))) (by decide)]
  rw [skyReducerYNodeCountUpdatedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "focusPtr" (.int (Int.ofNat (s.nodeCount + 2))) (by decide)]
  rw [skyReducerYFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "focusPtr" (skyReducerYOutVal s) (by decide)]
  rw [skyReducerYOutRefStoredState]
  exact skyReducerEntry_lookup_focusPtr s oracleVals

theorem skyReducerYStackSizeUpdatedState_lookup_stackSizePtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  rw [skyReducerYStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stackSizePtr" (.int (Int.ofNat (s.stack.length - 1))) (by decide)]
  rw [skyReducerYNodeCountUpdatedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "stackSizePtr" (.int (Int.ofNat (s.nodeCount + 2))) (by decide)]
  rw [skyReducerYFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "stackSizePtr" (skyReducerYOutVal s) (by decide)]
  rw [skyReducerYOutRefStoredState]
  exact skyReducerEntry_lookup_stackSizePtr s oracleVals

theorem skyReducerYStackSizeUpdatedState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  rw [skyReducerYStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCountPtr" (.int (Int.ofNat (s.stack.length - 1))) (by decide)]
  rw [skyReducerYNodeCountUpdatedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "nodeCountPtr" (.int (Int.ofNat (s.nodeCount + 2))) (by decide)]
  rw [skyReducerYFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCountPtr" (skyReducerYOutVal s) (by decide)]
  rw [skyReducerYOutRefStoredState]
  exact skyReducerEntry_lookup_nodeCountPtr s oracleVals

theorem skyReducerYStackSizeUpdatedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "nodeCount" =
      some (.int (Int.ofNat (s.nodeCount + 2))) := by
  rw [skyReducerYStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCount" (.int (Int.ofNat (s.stack.length - 1))) (by decide)]
  exact lookupVar_updateVar_eq (skyReducerYFocusUpdatedState s oracleVals hfocus hstack)
    "nodeCount" (.int (Int.ofNat (s.nodeCount + 2)))

theorem execStmt_yWriteFocusPtr_afterStackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2 (SKYLowering.writeScalar "focusPtr" (.var "focus"))
      (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYCommittedFocusState s oracleVals hfocus hstack)) := by
  simpa [skyReducerYCommittedFocusState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack) "focusPtr" "focus"
      (layoutForState s oracleVals).focusBase (skyReducerYOutVal s)
      (skyReducerYStackSizeUpdatedState_lookup_focusPtr s oracleVals hfocus hstack)
      (skyReducerYStackSizeUpdatedState_lookup_focus s oracleVals hfocus hstack))

theorem execStmt_yWriteStackSizePtr_afterFocusPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2 (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
      (skyReducerYCommittedFocusState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack)) := by
  have hPtr :
      (skyReducerYCommittedFocusState s oracleVals hfocus hstack).lookupVar "stackSizePtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
    simpa [skyReducerYCommittedFocusState] using
      (skyReducerYStackSizeUpdatedState_lookup_stackSizePtr s oracleVals hfocus hstack)
  have hVal :
      (skyReducerYCommittedFocusState s oracleVals hfocus hstack).lookupVar "stackSize" =
        some (.int (Int.ofNat (s.stack.length - 1))) := by
    simpa [skyReducerYCommittedFocusState] using
      (skyReducerYStackSizeUpdatedState_lookup_stackSize s oracleVals hfocus hstack)
  simpa [skyReducerYCommittedStackSizeState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerYCommittedFocusState s oracleVals hfocus hstack) "stackSizePtr" "stackSize"
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 1)))
      hPtr hVal)

theorem execStmt_yWriteNodeCountPtr_afterStackSizePtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 2 (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
      (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack) =
        some (.normal (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
  have hPtr :
      (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).lookupVar "nodeCountPtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
    simpa [skyReducerYCommittedStackSizeState, skyReducerYCommittedFocusState] using
      (skyReducerYStackSizeUpdatedState_lookup_nodeCountPtr s oracleVals hfocus hstack)
  have hVal :
      (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat (s.nodeCount + 2))) := by
    simpa [skyReducerYCommittedStackSizeState, skyReducerYCommittedFocusState] using
      (skyReducerYStackSizeUpdatedState_lookup_nodeCount s oracleVals hfocus hstack)
  simpa [skyReducerYCommittedState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack) "nodeCountPtr" "nodeCount"
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat (s.nodeCount + 2)))
      hPtr hVal)

theorem execStmt_yCommit_afterStackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    execStmt 4 (SKYLowering.commitAndReturn .progress)
      (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack) =
        some (.returned (.int StepStatus.progress.code) (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
  exact execStmt_commitAndReturn_of_steps .progress
    (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack)
    (skyReducerYCommittedFocusState s oracleVals hfocus hstack)
    (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack)
    (skyReducerYCommittedState s oracleVals hfocus hstack)
    (execStmt_yWriteFocusPtr_afterStackSize s oracleVals hfocus hstack)
    (execStmt_yWriteStackSizePtr_afterFocusPtr s oracleVals hfocus hstack)
    (execStmt_yWriteNodeCountPtr_afterStackSizePtr s oracleVals hfocus hstack)

theorem skyReducerYXLoadedState_lookup_maxNodes
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    (skyReducerYXLoadedState s oracleVals hfocus hstack).lookupVar "maxNodes" =
      some (.int (Int.ofNat s.maxNodes)) := by
  rw [skyReducerYXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "maxNodes" (skyReducerYXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "maxNodes" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "maxNodes" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "maxNodes" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "maxNodes" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_maxNodes s oracleVals

theorem execStmt_yCase_tagLoaded_progress
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) (hcap : s.nodeCount + 2 ≤ s.maxNodes) :
    execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.progress.code)
        (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
  have hGuardStack :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 1))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 1) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hge : (1 : Int) ≤ s.stack.length := by
      exact_mod_cast hstack
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 1))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 1) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 1 then 1 else 0)) := by
            rfl
      _ = some (.int 1) := by
            simp [hge]
  have hGuardCap :
      evalExpr (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 1) := by
    have hNodeCount :
        (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "nodeCount" =
          some (.int (Int.ofNat s.nodeCount)) := by
      rw [skyReducerAppTagLoadedState]
      rw [lookupVar_updateVar_ne _ "tag" "nodeCount" (.int (s.tags[s.focus]'hfocus)) (by decide)]
      exact skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals
    have hMaxNodes :
        (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "maxNodes" =
          some (.int (Int.ofNat s.maxNodes)) := by
      rw [skyReducerAppTagLoadedState]
      rw [lookupVar_updateVar_ne _ "tag" "maxNodes" (.int (s.tags[s.focus]'hfocus)) (by decide)]
      rw [skyReducerScalarsLoadedState]
      rw [lookupVar_updateVar_ne _ "nodeCount" "maxNodes" (.int (Int.ofNat s.nodeCount)) (by decide)]
      rw [skyReducerStackSizeLoadedState]
      rw [lookupVar_updateVar_ne _ "stackSize" "maxNodes" (.int (Int.ofNat s.stack.length)) (by decide)]
      rw [skyReducerFocusLoadedState]
      rw [lookupVar_updateVar_ne _ "focus" "maxNodes" (.int (Int.ofNat s.focus)) (by decide)]
      exact skyReducerEntry_lookup_maxNodes s oracleVals
    have hAdd :
        evalExpr (.binop .add (.var "nodeCount") (.intLit 2))
          (skyReducerAppTagLoadedState s oracleVals hfocus) =
            some (.int (Int.ofNat (s.nodeCount + 2))) := by
      calc
        evalExpr (.binop .add (.var "nodeCount") (.intLit 2))
            (skyReducerAppTagLoadedState s oracleVals hfocus)
          = evalBinOp .add (.int (Int.ofNat s.nodeCount)) (.int 2) := by
              simp [evalExpr, evalStaticExpr, hNodeCount]
        _ = some (.int (Int.ofNat (s.nodeCount + 2))) := by
              simpa [Int.ofNat_add] using
                (rfl :
                  evalBinOp .add (.int (Int.ofNat s.nodeCount)) (.int 2) =
                    some (.int (Int.ofNat s.nodeCount + 2)))
    have hle : (s.nodeCount + 2 : Int) ≤ s.maxNodes := by
      exact_mod_cast hcap
    calc
      evalExpr (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .le (.int (Int.ofNat (s.nodeCount + 2))) (.int (Int.ofNat s.maxNodes)) := by
            simp [evalExpr, evalStaticExpr, hAdd, hMaxNodes]
      _ = some (.int (if Int.ofNat (s.nodeCount + 2) ≤ Int.ofNat s.maxNodes then 1 else 0)) := by
            rfl
      _ = some (.int 1) := by
            simp [hle]
  calc
    execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 17
          (.ite
            (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
            (SKYLowering.seqs
              [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
              , .assign (.var "focus") (SKYLowering.nodeIx 1)
              , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
              , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
              , SKYLowering.commitAndReturn .progress ])
            (SKYLowering.commitAndReturn .outOfHeap))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.yCase, SKYLowering.seqs] using
              (execStmt_ite_of_eval_true
                (fuel := 17)
                (cond := (.binop .ge (.var "stackSize") (.intLit 1)))
                (th := (.ite
                  (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
                  (SKYLowering.seqs
                    [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                    , .assign (.var "focus") (SKYLowering.nodeIx 1)
                    , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.commitAndReturn .outOfHeap)))
                (el := SKYLowering.commitAndReturn .halted)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 1)
                hGuardStack
                (by simp [isTruthy]))
    _ = execStmt 16
          (SKYLowering.seqs
            [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.seqs] using
              (execStmt_ite_of_eval_true
                (fuel := 16)
                (cond := (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes")))
                (th := SKYLowering.seqs
                  [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                  , .assign (.var "focus") (SKYLowering.nodeIx 1)
                  , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                  , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                  , SKYLowering.commitAndReturn .progress ])
                (el := SKYLowering.commitAndReturn .outOfHeap)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 1)
                hGuardCap
                (by simp [isTruthy]))
    _ = execStmt 15
          (SKYLowering.seqs
            [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYXLoadedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 15
              (.assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1)))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 1)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (skyReducerYXLoadedState s oracleVals hfocus hstack)
              (execStmt_yLoadX_tagLoaded 15 s oracleVals hfocus hstack)
    _ = execStmt 14
          (SKYLowering.seqs
            [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYSelfTagStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 14
              (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr)
              (SKYLowering.seqs
                [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 1)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYXLoadedState s oracleVals hfocus hstack)
              (skyReducerYSelfTagStoredState s oracleVals hfocus hstack)
              (execStmt_yStoreSelfTag_afterLoadX s oracleVals hfocus hstack)
    _ = execStmt 13
          (SKYLowering.seqs
            [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 13
              (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus"))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 1)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYSelfTagStoredState s oracleVals hfocus hstack)
              (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack)
              (execStmt_yStoreSelfLhs_afterSelfTag s oracleVals hfocus hstack)
    _ = execStmt 12
          (SKYLowering.seqs
            [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 12
              (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x"))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 1)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack)
              (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack)
              (execStmt_yStoreSelfRhs_afterSelfLhs s oracleVals hfocus hstack)
    _ = execStmt 11
          (SKYLowering.seqs
            [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYSelfRefStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 11
              (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 1)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack)
              (skyReducerYSelfRefStoredState s oracleVals hfocus hstack)
              (execStmt_yStoreSelfRef_afterSelfRhs s oracleVals hfocus hstack)
    _ = execStmt 10
          (SKYLowering.seqs
            [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYOutTagStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 10
              (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr)
              (SKYLowering.seqs
                [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 1)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYSelfRefStoredState s oracleVals hfocus hstack)
              (skyReducerYOutTagStoredState s oracleVals hfocus hstack)
              (execStmt_yStoreOutTag_afterSelfRef s oracleVals hfocus hstack)
    _ = execStmt 9
          (SKYLowering.seqs
            [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYOutLhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 9
              (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x"))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 1)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYOutTagStoredState s oracleVals hfocus hstack)
              (skyReducerYOutLhsStoredState s oracleVals hfocus hstack)
              (execStmt_yStoreOutLhs_afterOutTag s oracleVals hfocus hstack)
    _ = execStmt 8
          (SKYLowering.seqs
            [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYOutRhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 8
              (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 1)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYOutLhsStoredState s oracleVals hfocus hstack)
              (skyReducerYOutRhsStoredState s oracleVals hfocus hstack)
              (execStmt_yStoreOutRhs_afterOutLhs s oracleVals hfocus hstack)
    _ = execStmt 7
          (SKYLowering.seqs
            [ .assign (.var "focus") (SKYLowering.nodeIx 1)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYOutRefStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 7
              (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0))
              (SKYLowering.seqs
                [ .assign (.var "focus") (SKYLowering.nodeIx 1)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYOutRhsStoredState s oracleVals hfocus hstack)
              (skyReducerYOutRefStoredState s oracleVals hfocus hstack)
              (execStmt_yStoreOutRef_afterOutRhs s oracleVals hfocus hstack)
    _ = execStmt 6
          (SKYLowering.seqs
            [ .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYFocusUpdatedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 6
              (.assign (.var "focus") (SKYLowering.nodeIx 1))
              (SKYLowering.seqs
                [ .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYOutRefStoredState s oracleVals hfocus hstack)
              (skyReducerYFocusUpdatedState s oracleVals hfocus hstack)
              (execStmt_ySetFocus_afterStores s oracleVals hfocus hstack)
    _ = execStmt 5
          (SKYLowering.seqs
            [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerYNodeCountUpdatedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 5
              (.assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2)))
              (SKYLowering.seqs
                [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerYFocusUpdatedState s oracleVals hfocus hstack)
              (skyReducerYNodeCountUpdatedState s oracleVals hfocus hstack)
              (execStmt_yIncNodeCount_afterFocus s oracleVals hfocus hstack)
    _ = execStmt 4 (SKYLowering.commitAndReturn .progress)
          (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 4
              (.assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1)))
              (SKYLowering.commitAndReturn .progress)
              (skyReducerYNodeCountUpdatedState s oracleVals hfocus hstack)
              (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack)
              (execStmt_yDecStackSize_afterNodeCount s oracleVals hfocus hstack)
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
            exact execStmt_yCommit_afterStackSize s oracleVals hfocus hstack

theorem execStmt_tagSwitch_y_of_tagLoaded
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 22
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
  simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
    skyReducerAppTagLoadedState, lookupVar_updateVar_eq, hy, NodeTag.code]

theorem execStmt_tagSwitch_y_of_tagLoaded_committed
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) (hcap : s.nodeCount + 2 ≤ s.maxNodes)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 22
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
  calc
    execStmt 22
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted))
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
          exact execStmt_tagSwitch_y_of_tagLoaded s oracleVals hfocus hy
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
          exact execStmt_yCase_tagLoaded_progress s oracleVals hfocus hstack hcap

theorem execStmt_yTagPrefix_skyReducerScalarsLoaded_committed
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 23
      (.seq
        (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted)))
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
  calc
    execStmt 23
        (.seq
          (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted)))
        (skyReducerScalarsLoadedState s oracleVals)
      = execStmt 22
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            exact execStmt_seq_of_normal 22
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted))
              (skyReducerScalarsLoadedState s oracleVals)
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (by
                simpa [execStmt, skyReducerAppTagLoadedState] using
                  execStmt_loadTag_skyReducerScalarsLoaded s oracleVals hwf hfocus)
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
          exact execStmt_tagSwitch_y_of_tagLoaded_committed s oracleVals hfocus hstack hcap hy

theorem execStmt_yPath_skyReducerEntry
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 27
      (.seq
        (.assign (.var "focus") (.deref (.var "focusPtr")))
        (.seq
          (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))))
      (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
  calc
    execStmt 27
        (.seq
          (.assign (.var "focus") (.deref (.var "focusPtr")))
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted)))))
        (skyReducerEntry s oracleVals)
      = execStmt 26
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))))
          (skyReducerFocusLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 26
              (.assign (.var "focus") (.deref (.var "focusPtr")))
              (.seq
                (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                (.seq
                  (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                  (.ite
                    (.binop .lt (.var "focus") (.var "nodeCount"))
                    (.seq
                      (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                      (switchMany (.var "tag")
                        [ (NodeTag.code .app, SKYLowering.appCase)
                        , (NodeTag.code .combK, SKYLowering.kCase)
                        , (NodeTag.code .combS, SKYLowering.sCase)
                        , (NodeTag.code .combY, SKYLowering.yCase)
                        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                        (SKYLowering.commitAndReturn .halted)))
                    (SKYLowering.commitAndReturn .halted))))
              (skyReducerEntry s oracleVals)
              (skyReducerFocusLoadedState s oracleVals)
              (by simpa [execStmt, skyReducerFocusLoadedState] using execStmt_loadFocus_skyReducerEntry s oracleVals)
    _ = execStmt 25
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerStackSizeLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 25
              (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
              (.seq
                (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                (.ite
                  (.binop .lt (.var "focus") (.var "nodeCount"))
                  (.seq
                    (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                    (switchMany (.var "tag")
                      [ (NodeTag.code .app, SKYLowering.appCase)
                      , (NodeTag.code .combK, SKYLowering.kCase)
                      , (NodeTag.code .combS, SKYLowering.sCase)
                      , (NodeTag.code .combY, SKYLowering.yCase)
                      , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                      (SKYLowering.commitAndReturn .halted)))
                  (SKYLowering.commitAndReturn .halted)))
              (skyReducerFocusLoadedState s oracleVals)
              (skyReducerStackSizeLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals)
    _ = execStmt 24
          (.ite
            (.binop .lt (.var "focus") (.var "nodeCount"))
            (.seq
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted)))
            (SKYLowering.commitAndReturn .halted))
          (skyReducerScalarsLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 24
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))
              (skyReducerStackSizeLoadedState s oracleVals)
              (skyReducerScalarsLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals)
    _ = execStmt 23
          (.seq
            (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
            (switchMany (.var "tag")
              [ (NodeTag.code .app, SKYLowering.appCase)
              , (NodeTag.code .combK, SKYLowering.kCase)
              , (NodeTag.code .combS, SKYLowering.sCase)
              , (NodeTag.code .combY, SKYLowering.yCase)
              , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerScalarsLoadedState s oracleVals) := by
            rw [execStmt_ite_of_eval_true
              (fuel := 23) (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
              (th := (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted))))
              (el := SKYLowering.commitAndReturn .halted)
              (st := skyReducerScalarsLoadedState s oracleVals)
              (v := .int (if s.focus < s.nodeCount then 1 else 0))]
            · exact skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals
            · simp [hfocus, isTruthy]
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
            exact execStmt_yTagPrefix_skyReducerScalarsLoaded_committed s oracleVals hwf hfocus hstack hcap hy

theorem execStmt_yPath_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 28 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerYCommittedState s oracleVals hfocus hstack)
            skyReducerLocals)) := by
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 27
          (SKYLowering.seqs
            [ .assign (.var "focus") (.deref (.var "focusPtr"))
            , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
            , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
            , .ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted) ])
          (enterBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            [ ("tag", .int)
            , ("focus", .int)
            , ("stackSize", .int)
            , ("nodeCount", .int)
            , ("x", .int)
            , ("y", .int)
            , ("z", .int)
            , ("ref", .int) ]) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerYCommittedState s oracleVals hfocus hstack)) := by
    simpa [SKYLowering.seqs, skyReducerEntry, skyReducerLocals] using
      (execStmt_yPath_skyReducerEntry s oracleVals hwf hfocus hstack hcap hy)
  rw [hbody]
  rfl

theorem execStmt_yPath_encodeExecState_fuel
    (extra : Nat) (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt (28 + extra) SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerYCommittedState s oracleVals hfocus hstack)
            skyReducerLocals)) := by
  exact execStmt_fuel_mono
    (h := execStmt_yPath_encodeExecState s oracleVals hwf hfocus hstack hcap hy)

theorem execStmt_yPath_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerYCommittedState s oracleVals hfocus hstack)
            skyReducerLocals)) := by
  simpa using execStmt_yPath_encodeExecState_fuel 372 s oracleVals hwf hfocus hstack hcap hy

theorem skyReducerTagLoadedState_eval_stackSecond
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (skyReducerOracleYVal s hstack) := by
  have hStackLookup :
      (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stack" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
    exact skyReducerAppTagLoadedState_lookup_stack s oracleVals hfocus
  have hStackSizeLookup :
      (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stackSize" =
        some (.int (Int.ofNat s.stack.length)) := by
    exact skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
  have hlen2 : 2 ≤ s.stack.length := hstack
  have hIdxLt : s.stack.length - 2 < s.stack.reverse.length := by
    simp
    omega
  have hSecondIdx : s.stack.length - 1 - (s.stack.length - 2) < s.stack.length := by
    omega
  have hSecond :
      s.stack.reverse.get ⟨s.stack.length - 2, hIdxLt⟩ =
        s.stack.get ⟨1, by omega⟩ := by
    have hEq : s.stack.length - 1 - (s.stack.length - 2) = 1 := by
      omega
    simpa [hEq] using
      (List.get_reverse' (l := s.stack) (n := ⟨s.stack.length - 2, hIdxLt⟩) (hn' := hSecondIdx))
  have hSub :
      evalExpr (SKYLowering.stackIx 2) (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.int (Int.ofNat (s.stack.length - 2))) := by
    calc
      evalExpr (SKYLowering.stackIx 2) (skyReducerAppTagLoadedState s oracleVals hfocus)
        = some (.int (Int.ofNat s.stack.length - 2)) := by
            simp [SKYLowering.stackIx, evalExpr, evalStaticExpr, hStackSizeLookup]
      _ = some (.int (Int.ofNat (s.stack.length - 2))) := by
            simp [Int.ofNat_sub hlen2]
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase))
        (.int (Int.ofNat (s.stack.length - 2))) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑(s.stack.length - 2) := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑(s.stack.length - 2) then
        some (CVal.ptr 0
          (Int.ofNat (layoutForState s oracleVals).stackBase + Int.ofNat (s.stack.length - 2)))
      else none) =
        some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 2))))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerAppTagLoadedState s oracleVals hfocus).readPtr
        { block := 0
          offset := Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) } =
      (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) := by
    simpa using
      (CState.readPtr_block0
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 2))
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)))
  have hHeapSame :
      (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) =
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) := by
    simp [skyReducerAppTagLoadedState, updateVar_heap]
  have hcell :
      readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) =
        some (s.stack.get ⟨1, by omega⟩) := by
    let h0 := writeIntList Heap.empty 0 s.tags.toList
    let h1 := writeNatList h0 s.maxNodes s.lhs.toList
    let h2 := writeNatList h1 (s.maxNodes + s.maxNodes) s.rhs.toList
    let h3 := writeNatList h2 (s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList
    let h4 := writeIntList h3 (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes)
      (oracleValuesPadded s oracleVals)
    let h5 := writeNatList h4
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals) s.stack.reverse
    let h6 := h5.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
      (.int (Int.ofNat s.focus))
    let h7 := h6.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
      (.int (Int.ofNat s.stack.length))
    let h8 := h7.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1)
      (.int (Int.ofNat s.nodeCount))
    have hcell' :
        readNatCell? h8
          (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 2)) =
            some (s.stack.get ⟨1, by omega⟩) := by
      simp only [h8, h7, h6]
      have haddrNeNodeCount :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 2) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeNodeCount]
      have haddrNeStackSize :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 2) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeStackSize]
      have haddrNeFocus :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 2) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeFocus]
      have hAt :
          readNatCell? h5
            (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length - 2)) =
            some (s.stack.reverse.get ⟨s.stack.length - 2, hIdxLt⟩) := by
        simpa [h5, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (readNatCell?_writeNatList_at
            (heap := h4)
            (base := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals)
            (xs := s.stack.reverse)
            (i := s.stack.length - 2)
            (by simpa using hIdxLt))
      calc
        readNatCell? h5
            (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length - 2))
          = some (s.stack.reverse.get ⟨s.stack.length - 2, hIdxLt⟩) := hAt
        _ = some (s.stack.get ⟨1, by omega⟩) := by
              simpa using congrArg some hSecond
    simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, encodeHeapWithLayout, encodeStackWithLayout,
      encodeOracleValuesWithLayout, encodeNodeArraysWithLayout, layoutForState, layoutFor]
      using hcell'
  have hHeap :
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) =
      some (.int (Int.ofNat (s.stack.get ⟨1, by omega⟩))) := by
    have hHeapEnc :
        (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) =
        some (.int (Int.ofNat (s.stack.get ⟨1, by omega⟩))) := by
      cases hread :
          (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
            ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) with
      | none =>
          simp [readNatCell?, readIntCell?, hread] at hcell
      | some v =>
          cases v with
          | int n =>
              simp [readNatCell?, readIntCell?, hread] at hcell
              have hn : n = Int.ofNat (s.stack.get ⟨1, by omega⟩) := by
                calc
                  n = Int.ofNat n.toNat := by
                    symm
                    exact Int.toNat_of_nonneg hcell.1
                  _ = Int.ofNat (s.stack.get ⟨1, by omega⟩) := by
                    simp [hcell.2]
              simp [hread, hn]
          | ptr block offset =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | uint n sz =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | float v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | null =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | undef =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | structVal fields =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | unionVal tag v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
    simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
      skyReducerEntry, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
      encodeExecStateWithLayout, layoutForState, layoutFor] using hHeapEnc
  calc
    evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) := by
            simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hStackLookup, hSub, hAdd] using hReadPtr
    _ = (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 2)) := hHeapSame
    _ = some (skyReducerOracleYVal s hstack) := by
          simp [skyReducerOracleYVal, hHeap]

theorem execStmt_oracleLoadX_tagLoaded
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt (fuel + 1)
      (.assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1)))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.normal (skyReducerOracleXLoadedState s oracleVals hfocus hstack)) := by
  have hEval :
      evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
        (skyReducerAppTagLoadedState s oracleVals hfocus) =
          some (skyReducerOracleXVal s hstack) := by
    simpa [skyReducerOracleXVal, skyReducerKXVal] using
      skyReducerTagLoadedState_eval_stackTop s oracleVals hfocus hstack
  simp [execStmt, skyReducerOracleXLoadedState, hEval]

theorem skyReducerOracleXLoadedState_lookup_stack
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerOracleXLoadedState s oracleVals hfocus hstack).lookupVar "stack" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
  rw [skyReducerOracleXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "stack"
      (skyReducerOracleXVal s hstack) (by decide : "stack" ≠ "x"))

theorem skyReducerOracleXLoadedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerOracleXLoadedState s oracleVals hfocus hstack).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerOracleXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "stackSize"
      (skyReducerOracleXVal s hstack) (by decide : "stackSize" ≠ "x"))

theorem execStmt_oracleLoadY_afterLoadX
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    execStmt (fuel + 1)
      (.assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2)))
      (skyReducerOracleXLoadedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerOracleXYLoadedState s oracleVals hfocus hstack)) := by
  have hEval :
      evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
        (skyReducerOracleXLoadedState s oracleVals hfocus hstack) =
          some (skyReducerOracleYVal s hstack) := by
    simpa [skyReducerOracleXLoadedState, SKYLowering.loadAt, SKYLowering.stackIx,
      evalExpr, evalStaticExpr, lookupVar_updateVar_ne, CState.findAllocByBlock,
      CState.readPtr, CState.resolvePtr, CState.readCell, updateVar_heap] using
      (skyReducerTagLoadedState_eval_stackSecond s oracleVals hfocus hstack)
  simp [execStmt, skyReducerOracleXYLoadedState, hEval]

theorem skyReducerOracleXYLoadedState_lookup_oracleRefs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerOracleXYLoadedState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
  rw [skyReducerOracleXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "oracleRefs" (skyReducerOracleYVal s hstack) (by decide)]
  rw [skyReducerOracleXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "oracleRefs"
      (skyReducerOracleXVal s hstack) (by decide : "oracleRefs" ≠ "x"))

theorem skyReducerOracleXYLoadedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    (skyReducerOracleXYLoadedState s oracleVals hfocus hstack).lookupVar "focus" =
      some (.int (Int.ofNat s.focus)) := by
  rw [skyReducerOracleXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "focus" (skyReducerOracleYVal s hstack) (by decide)]
  rw [skyReducerOracleXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "focus"
      (skyReducerOracleXVal s hstack) (by decide : "focus" ≠ "x"))

theorem execStmt_oracleLoadRef_afterLoadXY
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    execStmt (fuel + 1)
      (.assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus")))
      (skyReducerOracleXYLoadedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)) := by
  have hEvalTag :
      evalExpr (SKYLowering.loadAt "oracleRefs" (.var "focus"))
        (skyReducerAppTagLoadedState s oracleVals hfocus) =
          some (skyReducerOracleRefVal s hwf hfocus) := by
    simpa [skyReducerAppTagLoadedState, SKYLowering.loadAt, evalExpr, evalStaticExpr,
      lookupVar_updateVar_ne, CState.findAllocByBlock, CState.readPtr,
      CState.resolvePtr, CState.readCell, updateVar_heap, skyReducerOracleRefVal] using
      (skyReducerScalarsLoadedState_eval_oracleRefAtFocus s oracleVals hwf hfocus)
  have hEval :
      evalExpr (SKYLowering.loadAt "oracleRefs" (.var "focus"))
        (skyReducerOracleXYLoadedState s oracleVals hfocus hstack) =
          some (skyReducerOracleRefVal s hwf hfocus) := by
    simpa [skyReducerOracleXYLoadedState, skyReducerOracleXLoadedState, SKYLowering.loadAt,
      evalExpr, evalStaticExpr, lookupVar_updateVar_ne, CState.findAllocByBlock,
      CState.readPtr, CState.resolvePtr, CState.readCell, updateVar_heap] using
      hEvalTag
  simp [execStmt, skyReducerOracleXYRefLoadedState, hEval]

theorem readOracleValue_encodeHeapWithLayout
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    readIntCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
      ((layoutForState s oracleVals).oracleValsBase +
        s.oracleRefs[s.focus]'(by
          rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
          simpa [hrefs] using hfocus)) =
      some ((oracleVals[s.oracleRefs[s.focus]'(by
        rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
        simpa [hrefs] using hfocus)]?).getD 0) := by
  let ref := s.oracleRefs[s.focus]'(by
    rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
    simpa [hrefs] using hfocus)
  have href : ref < oracleSlotCount s oracleVals := by
    simpa [ref] using oracleRef_lt_oracleSlotCount s oracleVals hwf hfocus
  let h0 := writeIntList Heap.empty 0 s.tags.toList
  let h1 := writeNatList h0 s.maxNodes s.lhs.toList
  let h2 := writeNatList h1 (s.maxNodes + s.maxNodes) s.rhs.toList
  let h3 := writeNatList h2 (s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList
  let h4 := writeIntList h3 (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes)
    (oracleValuesPadded s oracleVals)
  let h5 := writeNatList h4
    (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals) s.stack.reverse
  let h6 := h5.write
    (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
    (.int (Int.ofNat s.focus))
  let h7 := h6.write
    (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
    (.int (Int.ofNat s.stack.length))
  let h8 := h7.write
    (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1)
    (.int (Int.ofNat s.nodeCount))
  have href' : ref < (oracleValuesPadded s oracleVals).length := by
    simpa [oracleValuesPadded_length] using href
  have hcell :
      readIntCell? h8
        (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + ref) =
      some ((oracleVals[ref]?).getD 0) := by
    simp only [h8, h7, h6]
    have haddrNeNodeCount :
        s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + ref ≠
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
            (s.stack.length + 1) + 1 + 1 := by
      omega
    rw [readIntCell?_write_other _ _ _ _ haddrNeNodeCount]
    have haddrNeStackSize :
        s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + ref ≠
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
            (s.stack.length + 1) + 1 := by
      omega
    rw [readIntCell?_write_other _ _ _ _ haddrNeStackSize]
    have haddrNeFocus :
        s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + ref ≠
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
            (s.stack.length + 1) := by
      omega
    rw [readIntCell?_write_other _ _ _ _ haddrNeFocus]
    have hstackBefore :
        s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + ref <
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals := by
      omega
    rw [writeNatList_readInt_before _ _ _ _ hstackBefore]
    simpa [h4, oracleValuesPadded, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (readIntCell?_writeIntList_at
        (heap := h3)
        (base := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes)
        (xs := oracleValuesPadded s oracleVals)
        (i := ref)
        href')
  simpa [ref, h0, h1, h2, h3, h4, h5, h6, h7, h8, encodeHeapWithLayout, encodeStackWithLayout,
    encodeOracleValuesWithLayout, encodeNodeArraysWithLayout, layoutForState, layoutFor] using hcell

set_option maxHeartbeats 10000000 in
theorem skyReducerOracleXYRefLoadedState_eval_oracleCond
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    evalExpr (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
      (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) =
        some (.int (if oracleArrayEval oracleVals
          (s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus))
          then 1 else 0)) := by
  have hOracleLookup :
      (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).lookupVar "oracleValues" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).oracleValsBase)) := by
    rw [skyReducerOracleXYRefLoadedState]
    rw [lookupVar_updateVar_ne _ "ref" "oracleValues" (skyReducerOracleRefVal s hwf hfocus) (by decide)]
    rw [skyReducerOracleXYLoadedState]
    rw [lookupVar_updateVar_ne _ "y" "oracleValues" (skyReducerOracleYVal s hstack) (by decide)]
    rw [skyReducerOracleXLoadedState]
    simpa using
      (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "oracleValues"
        (skyReducerOracleXVal s hstack) (by decide : "oracleValues" ≠ "x"))
  have hRefLookup :
      (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).lookupVar "ref" =
        some (skyReducerOracleRefVal s hwf hfocus) := by
    rw [skyReducerOracleXYRefLoadedState]
    simpa using
      (lookupVar_updateVar_eq (skyReducerOracleXYLoadedState s oracleVals hfocus hstack)
        "ref" (skyReducerOracleRefVal s hwf hfocus))
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).oracleValsBase))
        (skyReducerOracleRefVal s hwf hfocus) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).oracleValsBase +
        s.oracleRefs[s.focus]'(by
          rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
          simpa [hrefs] using hfocus)))) := by
    have hnonneg :
        0 ≤ (↑(layoutForState s oracleVals).oracleValsBase : Int) +
          ↑(s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus)) := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).oracleValsBase : Int) +
          ↑(s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus))
        then
          some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).oracleValsBase +
            s.oracleRefs[s.focus]'(by
              rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
              simpa [hrefs] using hfocus))))
        else none)
        =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).oracleValsBase +
        s.oracleRefs[s.focus]'(by
          rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
          simpa [hrefs] using hfocus))))
    simp [skyReducerOracleRefVal, hnonneg]
  have hReadPtr :
      (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).readPtr
        { block := 0
          offset := Int.ofNat ((layoutForState s oracleVals).oracleValsBase +
            s.oracleRefs[s.focus]'(by
              rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
              simpa [hrefs] using hfocus)) } =
      (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).heap.read
        ((layoutForState s oracleVals).oracleValsBase +
          s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus)) := by
    simpa using
      (CState.readPtr_block0
        (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)
        ((layoutForState s oracleVals).oracleValsBase +
          s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus))
        ((layoutForState s oracleVals).oracleValsBase +
          s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus)))
  have hLoadValue :
      evalExpr (SKYLowering.loadAt "oracleValues" (.var "ref"))
        (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) =
          some (.int ((oracleVals[s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus)]?).getD 0)) := by
    calc
      evalExpr (SKYLowering.loadAt "oracleValues" (.var "ref"))
          (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)
        = (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).heap.read
            ((layoutForState s oracleVals).oracleValsBase +
              s.oracleRefs[s.focus]'(by
                rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
                simpa [hrefs] using hfocus)) := by
              simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hOracleLookup, hRefLookup, hAdd] using
                hReadPtr
      _ = (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
            ((layoutForState s oracleVals).oracleValsBase +
              s.oracleRefs[s.focus]'(by
                rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
                simpa [hrefs] using hfocus)) := by
              simp [skyReducerOracleXYRefLoadedState, skyReducerOracleXYLoadedState,
                skyReducerOracleXLoadedState, updateVar_heap, skyReducerAppTagLoadedState,
                skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
                skyReducerEntry, encodeExecStateWithLayout, enterBlockState_heap]
      _ = some (.int ((oracleVals[s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus)]?).getD 0)) := by
              have hRead :=
                readOracleValue_encodeHeapWithLayout s oracleVals hwf hfocus
              cases hcell :
                  (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
                    ((layoutForState s oracleVals).oracleValsBase +
                      s.oracleRefs[s.focus]'(by
                        rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
                        simpa [hrefs] using hfocus)) with
              | none =>
                  simp [readIntCell?, hcell] at hRead
              | some v =>
                  cases v with
                  | int n =>
                      simp [readIntCell?, hcell] at hRead
                      simp [hcell, hRead]
                  | ptr block offset =>
                      simp [readIntCell?, hcell] at hRead
                  | uint n sz =>
                      simp [readIntCell?, hcell] at hRead
                  | float v =>
                      simp [readIntCell?, hcell] at hRead
                  | null =>
                      simp [readIntCell?, hcell] at hRead
                  | undef =>
                      simp [readIntCell?, hcell] at hRead
                  | structVal fields =>
                      simp [readIntCell?, hcell] at hRead
                  | unionVal tag v =>
                      simp [readIntCell?, hcell] at hRead
  let ref := s.oracleRefs[s.focus]'(by
    rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
    simpa [hrefs] using hfocus)
  have hStaticLoad :
      evalStaticExpr (SKYLowering.loadAt "oracleValues" (.var "ref")) = none := by
    simp [SKYLowering.loadAt, evalStaticExpr]
  calc
    evalExpr (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
        (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)
      = some (.int (if ((oracleVals[ref]?).getD 0) ≠ 0 then 1 else 0)) := by
          have hStaticCond :
              evalStaticExpr (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0)) =
                none := by
            simp [evalStaticExpr, SKYLowering.loadAt, hStaticLoad]
          have hZero :
              evalExpr (.intLit 0)
                (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) =
                  some (.int 0) := by
            simp [evalExpr, evalStaticExpr]
          rw [evalExpr, hStaticCond]
          · rw [hLoadValue, hZero]
            simpa [ref] using
              (HeytingLean.LeanCP.evalBinOp_ne_int_int (oracleVals[ref]?.getD 0) 0)
          · decide
          · decide
    _ = some (.int (if oracleArrayEval oracleVals ref then 1 else 0)) := by
          simp [oracleArrayEval_eq_getD_ne_zero]
    _ = some (.int (if oracleArrayEval oracleVals
          (s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus))
          then 1 else 0)) := by
          rfl

theorem skyReducerOracleXYRefLoadedState_lookup_x
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).lookupVar "x" =
      some (skyReducerOracleXVal s hstack) := by
  rw [skyReducerOracleXYRefLoadedState]
  rw [lookupVar_updateVar_ne _ "ref" "x" (skyReducerOracleRefVal s hwf hfocus) (by decide)]
  rw [skyReducerOracleXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "x" (skyReducerOracleYVal s hstack) (by decide)]
  rw [skyReducerOracleXLoadedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerAppTagLoadedState s oracleVals hfocus) "x" (skyReducerOracleXVal s hstack)

theorem skyReducerOracleXYRefLoadedState_lookup_y
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).lookupVar "y" =
      some (skyReducerOracleYVal s hstack) := by
  rw [skyReducerOracleXYRefLoadedState]
  rw [lookupVar_updateVar_ne _ "ref" "y" (skyReducerOracleRefVal s hwf hfocus) (by decide)]
  rw [skyReducerOracleXYLoadedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerOracleXLoadedState s oracleVals hfocus hstack) "y"
      (skyReducerOracleYVal s hstack)

theorem skyReducerOracleXYRefLoadedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerOracleXYRefLoadedState]
  rw [lookupVar_updateVar_ne _ "ref" "stackSize" (skyReducerOracleRefVal s hwf hfocus) (by decide)]
  rw [skyReducerOracleXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "stackSize" (skyReducerOracleYVal s hstack) (by decide)]
  rw [skyReducerOracleXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "stackSize" (skyReducerOracleXVal s hstack) (by decide)]
  exact skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus

theorem execStmt_oracleSetFocus_afterLoadRef
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length)
    (srcName : String) (target : CVal)
    (hSrc :
      (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack).lookupVar srcName = some target) :
    execStmt (fuel + 1) (.assign (.var "focus") (.var srcName))
      (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) =
        some (.normal (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack target)) := by
  simp [execStmt, evalExpr, evalStaticExpr, skyReducerOracleFocusUpdatedState, hSrc]

theorem execStmt_oracleDecStackSize_afterFocus
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    execStmt (fuel + 1)
      (.assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2)))
      (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack target) =
        some (.normal (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target)) := by
  have hlenge : 2 ≤ s.stack.length := hstack
  have hStackSize :
      (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack target).lookupVar "stackSize" =
        some (.int (Int.ofNat s.stack.length)) := by
    rw [skyReducerOracleFocusUpdatedState]
    rw [lookupVar_updateVar_ne _ "focus" "stackSize" target (by decide)]
    exact skyReducerOracleXYRefLoadedState_lookup_stackSize s oracleVals hwf hfocus hstack
  have hSub :
      evalBinOp .sub (.int (Int.ofNat s.stack.length)) (.int 2) =
        some (.int (Int.ofNat s.stack.length - 2)) := by
    rfl
  simpa [execStmt, evalExpr, evalStaticExpr, skyReducerOracleStackSizeUpdatedState,
    hStackSize, hSub, Int.ofNat_sub hlenge]

theorem skyReducerOracleStackSizeUpdatedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target).lookupVar "focus" =
      some target := by
  rw [skyReducerOracleStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focus" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerOracleFocusUpdatedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) "focus" target

theorem skyReducerOracleStackSizeUpdatedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target).lookupVar "stackSize" =
      some (.int (Int.ofNat (s.stack.length - 2))) := by
  rw [skyReducerOracleStackSizeUpdatedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack target)
      "stackSize" (.int (Int.ofNat (s.stack.length - 2)))

theorem skyReducerOracleStackSizeUpdatedState_lookup_focusPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  rw [skyReducerOracleStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focusPtr" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerOracleFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "focusPtr" target (by decide)]
  rw [skyReducerOracleXYRefLoadedState]
  rw [lookupVar_updateVar_ne _ "ref" "focusPtr" (skyReducerOracleRefVal s hwf hfocus) (by decide)]
  rw [skyReducerOracleXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "focusPtr" (skyReducerOracleYVal s hstack) (by decide)]
  rw [skyReducerOracleXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "focusPtr" (skyReducerOracleXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "focusPtr" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "focusPtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focusPtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "focusPtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_focusPtr s oracleVals

theorem skyReducerOracleStackSizeUpdatedState_lookup_stackSizePtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  rw [skyReducerOracleStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stackSizePtr" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerOracleFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "stackSizePtr" target (by decide)]
  rw [skyReducerOracleXYRefLoadedState]
  rw [lookupVar_updateVar_ne _ "ref" "stackSizePtr" (skyReducerOracleRefVal s hwf hfocus) (by decide)]
  rw [skyReducerOracleXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "stackSizePtr" (skyReducerOracleYVal s hstack) (by decide)]
  rw [skyReducerOracleXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "stackSizePtr" (skyReducerOracleXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "stackSizePtr" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "stackSizePtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stackSizePtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "stackSizePtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_stackSizePtr s oracleVals

theorem skyReducerOracleStackSizeUpdatedState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  rw [skyReducerOracleStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCountPtr" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerOracleFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCountPtr" target (by decide)]
  rw [skyReducerOracleXYRefLoadedState]
  rw [lookupVar_updateVar_ne _ "ref" "nodeCountPtr" (skyReducerOracleRefVal s hwf hfocus) (by decide)]
  rw [skyReducerOracleXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "nodeCountPtr" (skyReducerOracleYVal s hstack) (by decide)]
  rw [skyReducerOracleXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "nodeCountPtr" (skyReducerOracleXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "nodeCountPtr" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "nodeCountPtr" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCountPtr" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCountPtr" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_nodeCountPtr s oracleVals

theorem skyReducerOracleStackSizeUpdatedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerOracleStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCount" (.int (Int.ofNat (s.stack.length - 2))) (by decide)]
  rw [skyReducerOracleFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCount" target (by decide)]
  rw [skyReducerOracleXYRefLoadedState]
  rw [lookupVar_updateVar_ne _ "ref" "nodeCount" (skyReducerOracleRefVal s hwf hfocus) (by decide)]
  rw [skyReducerOracleXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "nodeCount" (skyReducerOracleYVal s hstack) (by decide)]
  rw [skyReducerOracleXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "nodeCount" (skyReducerOracleXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "nodeCount" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  exact skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals

theorem execStmt_oracleWriteFocusPtr_afterStackSize
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    execStmt 2 (SKYLowering.writeScalar "focusPtr" (.var "focus"))
      (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target) =
        some (.normal (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack target)) := by
  simpa [skyReducerOracleCommittedFocusState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target) "focusPtr" "focus"
      (layoutForState s oracleVals).focusBase target
      (skyReducerOracleStackSizeUpdatedState_lookup_focusPtr s oracleVals hwf hfocus hstack target)
      (skyReducerOracleStackSizeUpdatedState_lookup_focus s oracleVals hwf hfocus hstack target))

theorem execStmt_oracleWriteStackSizePtr_afterFocusPtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    execStmt 2 (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
      (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack target) =
        some (.normal (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack target)) := by
  have hPtr :
      (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack target).lookupVar "stackSizePtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
    simpa [skyReducerOracleCommittedFocusState] using
      (skyReducerOracleStackSizeUpdatedState_lookup_stackSizePtr s oracleVals hwf hfocus hstack target)
  have hVal :
      (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack target).lookupVar "stackSize" =
        some (.int (Int.ofNat (s.stack.length - 2))) := by
    simpa [skyReducerOracleCommittedFocusState] using
      (skyReducerOracleStackSizeUpdatedState_lookup_stackSize s oracleVals hwf hfocus hstack target)
  simpa [skyReducerOracleCommittedStackSizeState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack target) "stackSizePtr" "stackSize"
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))
      hPtr hVal)

theorem execStmt_oracleWriteNodeCountPtr_afterStackSizePtr
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    execStmt 2 (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack target) =
        some (.normal (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack target)) := by
  have hPtr :
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack target).lookupVar "nodeCountPtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
    simpa [skyReducerOracleCommittedStackSizeState, skyReducerOracleCommittedFocusState] using
      (skyReducerOracleStackSizeUpdatedState_lookup_nodeCountPtr s oracleVals hwf hfocus hstack target)
  have hVal :
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack target).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerOracleCommittedStackSizeState, skyReducerOracleCommittedFocusState] using
      (skyReducerOracleStackSizeUpdatedState_lookup_nodeCount s oracleVals hwf hfocus hstack target)
  simpa [skyReducerOracleCommittedState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack target) "nodeCountPtr" "nodeCount"
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))
      hPtr hVal)

theorem execStmt_oracleCommit_afterStackSize
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) (target : CVal) :
    execStmt 4 (SKYLowering.commitAndReturn .progress)
      (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack target)) := by
  exact execStmt_commitAndReturn_of_steps .progress
    (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack target)
    (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack target)
    (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack target)
    (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack target)
    (execStmt_oracleWriteFocusPtr_afterStackSize s oracleVals hwf hfocus hstack target)
    (execStmt_oracleWriteStackSizePtr_afterFocusPtr s oracleVals hwf hfocus hstack target)
    (execStmt_oracleWriteNodeCountPtr_afterStackSizePtr s oracleVals hwf hfocus hstack target)

theorem execStmt_oracleCase_tagLoaded
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    execStmt 11 SKYLowering.oracleCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.progress.code)
        (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
  let ref := s.oracleRefs[s.focus]'(by
    rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
    simpa [hrefs] using hfocus)
  have hGuard :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 2))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 1) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hge : (2 : Int) ≤ (s.stack.length : Int) := by
      exact_mod_cast hstack
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 2))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 2) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 2 then 1 else 0)) := by
            rfl
      _ = some (.int 1) := by
            simp [hge]
  by_cases horacle : oracleArrayEval oracleVals ref
  · calc
      execStmt 11 SKYLowering.oracleCase (skyReducerAppTagLoadedState s oracleVals hfocus)
        = execStmt 10
            (SKYLowering.seqs
              [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
              , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
              , .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
              , .ite
                  (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ]) ])
            (skyReducerAppTagLoadedState s oracleVals hfocus) := by
              simpa [SKYLowering.oracleCase, SKYLowering.seqs] using
                (execStmt_ite_of_eval_true
                  (fuel := 10)
                  (cond := (.binop .ge (.var "stackSize") (.intLit 2)))
                  (th := SKYLowering.seqs
                    [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                    , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                    , .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
                    , .ite
                        (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                        (SKYLowering.seqs
                          [ .assign (.var "focus") (.var "x")
                          , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                          , SKYLowering.commitAndReturn .progress ])
                        (SKYLowering.seqs
                          [ .assign (.var "focus") (.var "y")
                          , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                          , SKYLowering.commitAndReturn .progress ]) ])
                  (el := SKYLowering.commitAndReturn .halted)
                  (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                  (v := .int 1)
                  hGuard
                  (by simp [isTruthy]))
      _ = execStmt 9
            (SKYLowering.seqs
              [ .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
              , .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
              , .ite
                  (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ]) ])
            (skyReducerOracleXLoadedState s oracleVals hfocus hstack) := by
              exact execStmt_seq_of_normal 9
                (.assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1)))
                (SKYLowering.seqs
                  [ .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                  , .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
                  , .ite
                      (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "x")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ])
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "y")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ]) ])
                (skyReducerAppTagLoadedState s oracleVals hfocus)
                (skyReducerOracleXLoadedState s oracleVals hfocus hstack)
                (execStmt_oracleLoadX_tagLoaded 9 s oracleVals hfocus hstack)
      _ = execStmt 8
            (SKYLowering.seqs
              [ .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
              , .ite
                  (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ]) ])
            (skyReducerOracleXYLoadedState s oracleVals hfocus hstack) := by
              exact execStmt_seq_of_normal 8
                (.assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2)))
                (SKYLowering.seqs
                  [ .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
                  , .ite
                      (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "x")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ])
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "y")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ]) ])
                (skyReducerOracleXLoadedState s oracleVals hfocus hstack)
                (skyReducerOracleXYLoadedState s oracleVals hfocus hstack)
                (execStmt_oracleLoadY_afterLoadX 8 s oracleVals hfocus hstack)
      _ = execStmt 7
            (.ite
              (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
              (SKYLowering.seqs
                [ .assign (.var "focus") (.var "x")
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                , SKYLowering.commitAndReturn .progress ])
              (SKYLowering.seqs
                [ .assign (.var "focus") (.var "y")
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                , SKYLowering.commitAndReturn .progress ]))
            (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) := by
              exact execStmt_seq_of_normal 7
                (.assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus")))
                (.ite
                  (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ]))
                (skyReducerOracleXYLoadedState s oracleVals hfocus hstack)
                (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)
                (execStmt_oracleLoadRef_afterLoadXY 7 s oracleVals hwf hfocus hstack)
      _ = execStmt 6
            (SKYLowering.seqs
              [ .assign (.var "focus") (.var "x")
              , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
              , SKYLowering.commitAndReturn .progress ])
            (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) := by
              have hCond :
                  evalExpr (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                    (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) =
                      some (.int 1) := by
                simpa [ref, horacle] using
                  (skyReducerOracleXYRefLoadedState_eval_oracleCond s oracleVals hwf hfocus hstack)
              simpa [SKYLowering.seqs] using
                (execStmt_ite_of_eval_true
                  (fuel := 6)
                  (cond := (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0)))
                  (th := SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (el := SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (st := skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)
                  (v := .int 1)
                  hCond
                  (by simp [isTruthy]))
      _ = execStmt 5
            (SKYLowering.seqs
              [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
              , SKYLowering.commitAndReturn .progress ])
            (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleXVal s hstack)) := by
              exact execStmt_seq_of_normal 5
                (.assign (.var "focus") (.var "x"))
                (SKYLowering.seqs
                  [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                  , SKYLowering.commitAndReturn .progress ])
                (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)
                (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleXVal s hstack))
                (execStmt_oracleSetFocus_afterLoadRef 5 s oracleVals hwf hfocus hstack
                  "x" (skyReducerOracleXVal s hstack)
                  (skyReducerOracleXYRefLoadedState_lookup_x s oracleVals hwf hfocus hstack))
      _ = execStmt 4 (SKYLowering.commitAndReturn .progress)
            (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleXVal s hstack)) := by
              exact execStmt_seq_of_normal 4
                (.assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2)))
                (SKYLowering.commitAndReturn .progress)
                (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleXVal s hstack))
                (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleXVal s hstack))
                (execStmt_oracleDecStackSize_afterFocus 4 s oracleVals hwf hfocus hstack (skyReducerOracleXVal s hstack))
      _ = some (.returned (.int StepStatus.progress.code)
            (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack (skyReducerOracleXVal s hstack))) := by
              exact execStmt_oracleCommit_afterStackSize s oracleVals hwf hfocus hstack (skyReducerOracleXVal s hstack)
      _ = some (.returned (.int StepStatus.progress.code)
            (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
              (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
              simp [skyReducerOracleTargetVal, skyReducerOracleTargetNat, ref, horacle, skyReducerOracleXVal]
  · calc
      execStmt 11 SKYLowering.oracleCase (skyReducerAppTagLoadedState s oracleVals hfocus)
        = execStmt 10
            (SKYLowering.seqs
              [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
              , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
              , .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
              , .ite
                  (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ]) ])
            (skyReducerAppTagLoadedState s oracleVals hfocus) := by
              simpa [SKYLowering.oracleCase, SKYLowering.seqs] using
                (execStmt_ite_of_eval_true
                  (fuel := 10)
                  (cond := (.binop .ge (.var "stackSize") (.intLit 2)))
                  (th := SKYLowering.seqs
                    [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                    , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                    , .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
                    , .ite
                        (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                        (SKYLowering.seqs
                          [ .assign (.var "focus") (.var "x")
                          , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                          , SKYLowering.commitAndReturn .progress ])
                        (SKYLowering.seqs
                          [ .assign (.var "focus") (.var "y")
                          , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                          , SKYLowering.commitAndReturn .progress ]) ])
                  (el := SKYLowering.commitAndReturn .halted)
                  (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                  (v := .int 1)
                  hGuard
                  (by simp [isTruthy]))
      _ = execStmt 9
            (SKYLowering.seqs
              [ .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
              , .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
              , .ite
                  (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ]) ])
            (skyReducerOracleXLoadedState s oracleVals hfocus hstack) := by
              exact execStmt_seq_of_normal 9
                (.assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1)))
                (SKYLowering.seqs
                  [ .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                  , .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
                  , .ite
                      (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "x")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ])
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "y")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ]) ])
                (skyReducerAppTagLoadedState s oracleVals hfocus)
                (skyReducerOracleXLoadedState s oracleVals hfocus hstack)
                (execStmt_oracleLoadX_tagLoaded 9 s oracleVals hfocus hstack)
      _ = execStmt 8
            (SKYLowering.seqs
              [ .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
              , .ite
                  (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ]) ])
            (skyReducerOracleXYLoadedState s oracleVals hfocus hstack) := by
              exact execStmt_seq_of_normal 8
                (.assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2)))
                (SKYLowering.seqs
                  [ .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
                  , .ite
                      (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "x")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ])
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "y")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ]) ])
                (skyReducerOracleXLoadedState s oracleVals hfocus hstack)
                (skyReducerOracleXYLoadedState s oracleVals hfocus hstack)
                (execStmt_oracleLoadY_afterLoadX 8 s oracleVals hfocus hstack)
      _ = execStmt 7
            (.ite
              (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
              (SKYLowering.seqs
                [ .assign (.var "focus") (.var "x")
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                , SKYLowering.commitAndReturn .progress ])
              (SKYLowering.seqs
                [ .assign (.var "focus") (.var "y")
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                , SKYLowering.commitAndReturn .progress ]))
            (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) := by
              exact execStmt_seq_of_normal 7
                (.assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus")))
                (.ite
                  (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ]))
                (skyReducerOracleXYLoadedState s oracleVals hfocus hstack)
                (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)
                (execStmt_oracleLoadRef_afterLoadXY 7 s oracleVals hwf hfocus hstack)
      _ = execStmt 6
            (SKYLowering.seqs
              [ .assign (.var "focus") (.var "y")
              , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
              , SKYLowering.commitAndReturn .progress ])
            (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) := by
              have hCond :
                  evalExpr (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                    (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack) =
                      some (.int 0) := by
                simpa [ref, horacle] using
                  (skyReducerOracleXYRefLoadedState_eval_oracleCond s oracleVals hwf hfocus hstack)
              simpa [SKYLowering.seqs] using
                (execStmt_ite_of_eval_false
                  (fuel := 6)
                  (cond := (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0)))
                  (th := SKYLowering.seqs
                    [ .assign (.var "focus") (.var "x")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (el := SKYLowering.seqs
                    [ .assign (.var "focus") (.var "y")
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                    , SKYLowering.commitAndReturn .progress ])
                  (st := skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)
                  (v := .int 0)
                  hCond
                  (by simp [isTruthy]))
      _ = execStmt 5
            (SKYLowering.seqs
              [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
              , SKYLowering.commitAndReturn .progress ])
            (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleYVal s hstack)) := by
              exact execStmt_seq_of_normal 5
                (.assign (.var "focus") (.var "y"))
                (SKYLowering.seqs
                  [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                  , SKYLowering.commitAndReturn .progress ])
                (skyReducerOracleXYRefLoadedState s oracleVals hwf hfocus hstack)
                (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleYVal s hstack))
                (execStmt_oracleSetFocus_afterLoadRef 5 s oracleVals hwf hfocus hstack
                  "y" (skyReducerOracleYVal s hstack)
                  (skyReducerOracleXYRefLoadedState_lookup_y s oracleVals hwf hfocus hstack))
      _ = execStmt 4 (SKYLowering.commitAndReturn .progress)
            (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleYVal s hstack)) := by
              exact execStmt_seq_of_normal 4
                (.assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2)))
                (SKYLowering.commitAndReturn .progress)
                (skyReducerOracleFocusUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleYVal s hstack))
                (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack (skyReducerOracleYVal s hstack))
                (execStmt_oracleDecStackSize_afterFocus 4 s oracleVals hwf hfocus hstack (skyReducerOracleYVal s hstack))
      _ = some (.returned (.int StepStatus.progress.code)
            (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack (skyReducerOracleYVal s hstack))) := by
              exact execStmt_oracleCommit_afterStackSize s oracleVals hwf hfocus hstack (skyReducerOracleYVal s hstack)
      _ = some (.returned (.int StepStatus.progress.code)
            (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
              (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
              simp [skyReducerOracleTargetVal, skyReducerOracleTargetNat, ref, horacle, skyReducerOracleYVal]

theorem execStmt_tagSwitch_oracle_of_tagLoaded
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    execStmt 16
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        execStmt 11 SKYLowering.oracleCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
  simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
    skyReducerAppTagLoadedState, lookupVar_updateVar_eq, horacleTag, NodeTag.code]

theorem execStmt_tagSwitch_oracle_of_tagLoaded_committed
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length)
    (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    execStmt 16
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
            (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
  calc
    execStmt 16
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted))
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 11 SKYLowering.oracleCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
          exact execStmt_tagSwitch_oracle_of_tagLoaded s oracleVals hfocus horacleTag
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
            (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
          exact execStmt_oracleCase_tagLoaded s oracleVals hwf hfocus hstack

theorem execStmt_oracleTagPrefix_skyReducerScalarsLoaded_committed
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    execStmt 17
      (.seq
        (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted)))
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
            (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
  calc
    execStmt 17
        (.seq
          (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted)))
        (skyReducerScalarsLoadedState s oracleVals)
      = execStmt 16
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            exact execStmt_seq_of_normal 16
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted))
              (skyReducerScalarsLoadedState s oracleVals)
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (by
                simpa [execStmt, skyReducerAppTagLoadedState] using
                  execStmt_loadTag_skyReducerScalarsLoaded s oracleVals hwf hfocus)
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
            (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
          exact execStmt_tagSwitch_oracle_of_tagLoaded_committed s oracleVals hwf hfocus hstack horacleTag

theorem execStmt_oraclePath_skyReducerEntry
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    execStmt 21
      (.seq
        (.assign (.var "focus") (.deref (.var "focusPtr")))
        (.seq
          (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))))
      (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
            (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
  calc
    execStmt 21
        (.seq
          (.assign (.var "focus") (.deref (.var "focusPtr")))
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted)))))
        (skyReducerEntry s oracleVals)
      = execStmt 17
          (.seq
            (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
            (switchMany (.var "tag")
              [ (NodeTag.code .app, SKYLowering.appCase)
              , (NodeTag.code .combK, SKYLowering.kCase)
              , (NodeTag.code .combS, SKYLowering.sCase)
              , (NodeTag.code .combY, SKYLowering.yCase)
              , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerScalarsLoadedState s oracleVals) := by
            calc
              execStmt 21
                  (.seq
                    (.assign (.var "focus") (.deref (.var "focusPtr")))
                    (.seq
                      (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                      (.seq
                        (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                        (.ite
                          (.binop .lt (.var "focus") (.var "nodeCount"))
                          (.seq
                            (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                            (switchMany (.var "tag")
                              [ (NodeTag.code .app, SKYLowering.appCase)
                              , (NodeTag.code .combK, SKYLowering.kCase)
                              , (NodeTag.code .combS, SKYLowering.sCase)
                              , (NodeTag.code .combY, SKYLowering.yCase)
                              , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                              (SKYLowering.commitAndReturn .halted)))
                          (SKYLowering.commitAndReturn .halted)))))
                  (skyReducerEntry s oracleVals)
                = execStmt 20
                    (.seq
                      (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                      (.seq
                        (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                        (.ite
                          (.binop .lt (.var "focus") (.var "nodeCount"))
                          (.seq
                            (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                            (switchMany (.var "tag")
                              [ (NodeTag.code .app, SKYLowering.appCase)
                              , (NodeTag.code .combK, SKYLowering.kCase)
                              , (NodeTag.code .combS, SKYLowering.sCase)
                              , (NodeTag.code .combY, SKYLowering.yCase)
                              , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                              (SKYLowering.commitAndReturn .halted)))
                          (SKYLowering.commitAndReturn .halted))))
                    (skyReducerFocusLoadedState s oracleVals) := by
                      exact execStmt_seq_of_normal 20
                        (.assign (.var "focus") (.deref (.var "focusPtr")))
                        (.seq
                          (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                          (.seq
                            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                            (.ite
                              (.binop .lt (.var "focus") (.var "nodeCount"))
                              (.seq
                                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                                (switchMany (.var "tag")
                                  [ (NodeTag.code .app, SKYLowering.appCase)
                                  , (NodeTag.code .combK, SKYLowering.kCase)
                                  , (NodeTag.code .combS, SKYLowering.sCase)
                                  , (NodeTag.code .combY, SKYLowering.yCase)
                                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                                  (SKYLowering.commitAndReturn .halted)))
                              (SKYLowering.commitAndReturn .halted))))
                        (skyReducerEntry s oracleVals)
                        (skyReducerFocusLoadedState s oracleVals)
                        (by simpa [execStmt, skyReducerFocusLoadedState] using execStmt_loadFocus_skyReducerEntry s oracleVals)
              _ = execStmt 19
                    (.seq
                      (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                      (.ite
                        (.binop .lt (.var "focus") (.var "nodeCount"))
                        (.seq
                          (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                          (switchMany (.var "tag")
                            [ (NodeTag.code .app, SKYLowering.appCase)
                            , (NodeTag.code .combK, SKYLowering.kCase)
                            , (NodeTag.code .combS, SKYLowering.sCase)
                            , (NodeTag.code .combY, SKYLowering.yCase)
                            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                            (SKYLowering.commitAndReturn .halted)))
                        (SKYLowering.commitAndReturn .halted)))
                    (skyReducerStackSizeLoadedState s oracleVals) := by
                      exact execStmt_seq_of_normal 19
                        (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                        (.seq
                          (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                          (.ite
                            (.binop .lt (.var "focus") (.var "nodeCount"))
                            (.seq
                              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                              (switchMany (.var "tag")
                                [ (NodeTag.code .app, SKYLowering.appCase)
                                , (NodeTag.code .combK, SKYLowering.kCase)
                                , (NodeTag.code .combS, SKYLowering.sCase)
                                , (NodeTag.code .combY, SKYLowering.yCase)
                                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                                (SKYLowering.commitAndReturn .halted)))
                            (SKYLowering.commitAndReturn .halted)))
                        (skyReducerFocusLoadedState s oracleVals)
                        (skyReducerStackSizeLoadedState s oracleVals)
                        (by simpa [execStmt] using execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals)
              _ = execStmt 18
                    (.ite
                      (.binop .lt (.var "focus") (.var "nodeCount"))
                      (.seq
                        (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                        (switchMany (.var "tag")
                          [ (NodeTag.code .app, SKYLowering.appCase)
                          , (NodeTag.code .combK, SKYLowering.kCase)
                          , (NodeTag.code .combS, SKYLowering.sCase)
                          , (NodeTag.code .combY, SKYLowering.yCase)
                          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                          (SKYLowering.commitAndReturn .halted)))
                      (SKYLowering.commitAndReturn .halted))
                    (skyReducerScalarsLoadedState s oracleVals) := by
                      exact execStmt_seq_of_normal 18
                        (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                        (.ite
                          (.binop .lt (.var "focus") (.var "nodeCount"))
                          (.seq
                            (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                            (switchMany (.var "tag")
                              [ (NodeTag.code .app, SKYLowering.appCase)
                              , (NodeTag.code .combK, SKYLowering.kCase)
                              , (NodeTag.code .combS, SKYLowering.sCase)
                              , (NodeTag.code .combY, SKYLowering.yCase)
                              , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                              (SKYLowering.commitAndReturn .halted)))
                          (SKYLowering.commitAndReturn .halted))
                        (skyReducerStackSizeLoadedState s oracleVals)
                        (skyReducerScalarsLoadedState s oracleVals)
                        (by simpa [execStmt] using execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals)
              _ = execStmt 17
                    (.seq
                      (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                      (switchMany (.var "tag")
                        [ (NodeTag.code .app, SKYLowering.appCase)
                        , (NodeTag.code .combK, SKYLowering.kCase)
                        , (NodeTag.code .combS, SKYLowering.sCase)
                        , (NodeTag.code .combY, SKYLowering.yCase)
                        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                        (SKYLowering.commitAndReturn .halted)))
                    (skyReducerScalarsLoadedState s oracleVals) := by
                      rw [execStmt_ite_of_eval_true
                        (fuel := 17) (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
                        (th := (.seq
                          (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                          (switchMany (.var "tag")
                            [ (NodeTag.code .app, SKYLowering.appCase)
                            , (NodeTag.code .combK, SKYLowering.kCase)
                            , (NodeTag.code .combS, SKYLowering.sCase)
                            , (NodeTag.code .combY, SKYLowering.yCase)
                            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                            (SKYLowering.commitAndReturn .halted))))
                        (el := SKYLowering.commitAndReturn .halted)
                        (st := skyReducerScalarsLoadedState s oracleVals)
                        (v := .int (if s.focus < s.nodeCount then 1 else 0))]
                      · exact skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals
                      · simp [hfocus, isTruthy]
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
            (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
          exact execStmt_oracleTagPrefix_skyReducerScalarsLoaded_committed s oracleVals hwf hfocus hstack horacleTag

theorem execStmt_oraclePath_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    execStmt 22 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
              (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))
            skyReducerLocals)) := by
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 21
          (SKYLowering.seqs
            [ .assign (.var "focus") (.deref (.var "focusPtr"))
            , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
            , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
            , .ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted) ])
          (enterBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            [ ("tag", .int)
            , ("focus", .int)
            , ("stackSize", .int)
            , ("nodeCount", .int)
            , ("x", .int)
            , ("y", .int)
            , ("z", .int)
            , ("ref", .int) ]) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
            (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))) := by
    simpa [SKYLowering.seqs, skyReducerEntry, skyReducerLocals] using
      (execStmt_oraclePath_skyReducerEntry s oracleVals hwf hfocus hstack horacleTag)
  rw [hbody]
  rfl

theorem execStmt_oraclePath_encodeExecState_fuel
    (extra : Nat) (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length)
    (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    execStmt (22 + extra) SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
              (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))
            skyReducerLocals)) := by
  exact execStmt_fuel_mono
    (h := execStmt_oraclePath_encodeExecState s oracleVals hwf hfocus hstack horacleTag)

theorem execStmt_oraclePath_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length)
    (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
              (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack))
            skyReducerLocals)) := by
  simpa using execStmt_oraclePath_encodeExecState_fuel 378 s oracleVals hwf hfocus hstack horacleTag

theorem readIntArray?_write_other (heap : Heap) (writeAddr : Nat) (v : CVal)
    (base count : Nat) (hdisj : writeAddr < base ∨ base + count ≤ writeAddr) :
    readIntArray? (heap.write writeAddr v) base count = readIntArray? heap base count := by
  simp [readIntArray?, readIntList?_write_other, hdisj]

theorem readNatArray?_write_other (heap : Heap) (writeAddr : Nat) (v : CVal)
    (base count : Nat) (hdisj : writeAddr < base ∨ base + count ≤ writeAddr) :
    readNatArray? (heap.write writeAddr v) base count = readNatArray? heap base count := by
  simp [readNatArray?, readNatList?_write_other, hdisj]

theorem readIntArray?_writeIntList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Int)
    (base count : Nat) (hdisj : base + count ≤ writeBase) :
    readIntArray? (writeIntList heap writeBase xs) base count = readIntArray? heap base count := by
  simp [readIntArray?, readIntList?_writeIntList_otherRange, hdisj]

theorem readIntArray?_writeNatList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Nat)
    (base count : Nat) (hdisj : base + count ≤ writeBase) :
    readIntArray? (writeNatList heap writeBase xs) base count = readIntArray? heap base count := by
  simp [readIntArray?, readIntList?_writeNatList_otherRange, hdisj]

theorem readNatArray?_writeIntList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Int)
    (base count : Nat) (hdisj : base + count ≤ writeBase) :
    readNatArray? (writeIntList heap writeBase xs) base count = readNatArray? heap base count := by
  simp [readNatArray?, readNatList?_writeIntList_otherRange, hdisj]

theorem readNatArray?_writeNatList_otherRange (heap : Heap) (writeBase : Nat) (xs : List Nat)
    (base count : Nat) (hdisj : base + count ≤ writeBase) :
    readNatArray? (writeNatList heap writeBase xs) base count = readNatArray? heap base count := by
  simp [readNatArray?, readNatList?_writeNatList_otherRange, hdisj]

@[simp] theorem readIntArray?_writeIntList (heap : Heap) (base : Nat) (xs : List Int) :
    readIntArray? (writeIntList heap base xs) base xs.length = some xs.toArray := by
  simp [readIntArray?, readIntList?_writeIntList]

@[simp] theorem readNatArray?_writeNatList (heap : Heap) (base : Nat) (xs : List Nat) :
    readNatArray? (writeNatList heap base xs) base xs.length = some xs.toArray := by
  simp [readNatArray?, readNatList?_writeNatList]

theorem readIntList?_append_one_at_end_map
    (heap : Heap) (base count : Nat) (a : Int) :
    readIntList?
        (heap.write (base + count) (.int a))
        base (count + 1) =
      Option.map (fun xs => xs ++ [a]) (readIntList? heap base count) := by
  induction count generalizing heap base with
  | zero =>
      simp [readIntList?, readIntCell?, Heap.read, Heap.write]
  | succ count ih =>
      rw [readIntList?]
      rw [readIntCell?_write_other
          (heap := heap)
          (readAddr := base)
          (writeAddr := base + (count + 1))
          (v := .int a) (by omega)]
      have htail :
          readIntList?
              (heap.write (base + (count + 1)) (.int a))
              (base + 1) (count + 1) =
            Option.map (fun xs => xs ++ [a]) (readIntList? heap (base + 1) count) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ih (heap := heap) (base := base + 1)
      rw [htail]
      cases hcell : readIntCell? heap base <;>
        cases htailRead : readIntList? heap (base + 1) count <;>
        simp [readIntList?, hcell, htailRead]

theorem readIntArray?_append_one_at_end
    (heap : Heap) (base count : Nat) (xs : Array Int) (a : Int)
    (hread : readIntArray? heap base count = some xs) :
    readIntArray?
        (heap.write (base + count) (.int a))
        base (count + 1) =
      some (xs.push a) := by
  cases hlist : readIntList? heap base count with
  | none =>
      simp [readIntArray?, hlist] at hread
  | some ys =>
      have hxs : ys.toArray = xs := by
        simp [readIntArray?, hlist] at hread
        exact hread
      rw [readIntArray?, readIntList?_append_one_at_end_map]
      simp [hlist]
      calc
        (ys ++ [a]).toArray = ys.toArray.push a := by
          simpa using array_toArray_append_one_eq_push ys.toArray a
        _ = xs.push a := by
          simpa [hxs]

theorem readIntList?_append_two_at_end_map
    (heap : Heap) (base count : Nat) (a b : Int) :
    readIntList?
        (((heap.write (base + count) (.int a)).write (base + count + 1) (.int b)))
        base (count + 2) =
      Option.map (fun xs => xs ++ [a, b]) (readIntList? heap base count) := by
  induction count generalizing heap base with
  | zero =>
      simp [readIntList?, readIntCell?, Heap.read, Heap.write]
  | succ count ih =>
      rw [readIntList?]
      rw [readIntCell?_write_other
          (heap := heap.write (base + (count + 1)) (.int a))
          (readAddr := base)
          (writeAddr := base + (count + 1) + 1)
          (v := .int b) (by omega)]
      rw [readIntCell?_write_other
          (heap := heap)
          (readAddr := base)
          (writeAddr := base + (count + 1))
          (v := .int a) (by omega)]
      have htail :
          readIntList?
              (((heap.write (base + (count + 1)) (.int a)).write
                  (base + (count + 1) + 1) (.int b)))
              (base + 1) (count + 2) =
            Option.map (fun xs => xs ++ [a, b]) (readIntList? heap (base + 1) count) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ih (heap := heap) (base := base + 1)
      rw [htail]
      cases hcell : readIntCell? heap base <;>
        cases htailRead : readIntList? heap (base + 1) count <;>
        simp [readIntList?, hcell, htailRead]

theorem readIntList?_append_two_at_end
    (heap : Heap) (base count : Nat) (xs : List Int) (a b : Int)
    (hread : readIntList? heap base count = some xs) :
    readIntList?
        (((heap.write (base + count) (.int a)).write (base + count + 1) (.int b)))
        base (count + 2) =
      some (xs ++ [a, b]) := by
  rw [readIntList?_append_two_at_end_map]
  simp [hread]

theorem readIntArray?_append_two_at_end
    (heap : Heap) (base count : Nat) (xs : Array Int) (a b : Int)
    (hread : readIntArray? heap base count = some xs) :
    readIntArray?
        (((heap.write (base + count) (.int a)).write (base + count + 1) (.int b)))
        base (count + 2) =
      some ((xs.push a).push b) := by
  cases hlist : readIntList? heap base count with
  | none =>
      simp [readIntArray?, hlist] at hread
  | some ys =>
      have hxs : ys.toArray = xs := by
        simp [readIntArray?, hlist] at hread
        exact hread
      rw [readIntArray?, readIntList?_append_two_at_end_map]
      simp [hlist]
      calc
        (ys ++ [a, b]).toArray = (ys.toArray.push a).push b := by
          simpa using array_toArray_append_two_eq_push_push ys.toArray a b
        _ = (xs.push a).push b := by
          simpa [hxs]

theorem readIntArray?_append_three_at_end
    (heap : Heap) (base count : Nat) (xs : Array Int) (a b c : Int)
    (hread : readIntArray? heap base count = some xs) :
    readIntArray?
        ((((heap.write (base + count) (.int a)).write (base + count + 1) (.int b)).write
            (base + count + 2) (.int c)))
        base (count + 3) =
      some (((xs.push a).push b).push c) := by
  have htwo :
      readIntArray?
          (((heap.write (base + count) (.int a)).write (base + count + 1) (.int b)))
          base (count + 2) =
        some ((xs.push a).push b) := by
    exact readIntArray?_append_two_at_end heap base count xs a b hread
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (readIntArray?_append_one_at_end
      (heap := ((heap.write (base + count) (.int a)).write (base + count + 1) (.int b)))
      (base := base) (count := count + 2) (xs := (xs.push a).push b) (a := c) htwo)

theorem readNatList?_append_one_at_end_map
    (heap : Heap) (base count a : Nat) :
    readNatList?
        (heap.write (base + count) (.int (Int.ofNat a)))
        base (count + 1) =
      Option.map (fun xs => xs ++ [a]) (readNatList? heap base count) := by
  induction count generalizing heap base with
  | zero =>
      simp [readNatList?, readNatCell?, readIntCell?, Heap.read, Heap.write]
  | succ count ih =>
      rw [readNatList?]
      rw [readNatCell?_write_other
          (heap := heap)
          (readAddr := base)
          (writeAddr := base + (count + 1))
          (v := .int (Int.ofNat a)) (by omega)]
      have htail :
          readNatList?
              (heap.write (base + (count + 1)) (.int (Int.ofNat a)))
              (base + 1) (count + 1) =
            Option.map (fun xs => xs ++ [a]) (readNatList? heap (base + 1) count) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ih (heap := heap) (base := base + 1)
      rw [htail]
      cases hcell : readNatCell? heap base <;>
        cases htailRead : readNatList? heap (base + 1) count <;>
        simp [readNatList?, hcell, htailRead]

theorem readNatList?_append_two_at_end_map
    (heap : Heap) (base count a b : Nat) :
    readNatList?
        (((heap.write (base + count) (.int (Int.ofNat a))).write
            (base + count + 1) (.int (Int.ofNat b))))
        base (count + 2) =
      Option.map (fun xs => xs ++ [a, b]) (readNatList? heap base count) := by
  induction count generalizing heap base with
  | zero =>
      simp [readNatList?, readNatCell?, readIntCell?, Heap.read, Heap.write]
  | succ count ih =>
      rw [readNatList?]
      rw [readNatCell?_write_other
          (heap := heap.write (base + (count + 1)) (.int (Int.ofNat a)))
          (readAddr := base)
          (writeAddr := base + (count + 1) + 1)
          (v := .int (Int.ofNat b)) (by omega)]
      rw [readNatCell?_write_other
          (heap := heap)
          (readAddr := base)
          (writeAddr := base + (count + 1))
          (v := .int (Int.ofNat a)) (by omega)]
      have htail :
          readNatList?
              (((heap.write (base + (count + 1)) (.int (Int.ofNat a))).write
                  (base + (count + 1) + 1) (.int (Int.ofNat b))))
              (base + 1) (count + 2) =
            Option.map (fun xs => xs ++ [a, b]) (readNatList? heap (base + 1) count) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ih (heap := heap) (base := base + 1)
      rw [htail]
      cases hcell : readNatCell? heap base <;>
        cases htailRead : readNatList? heap (base + 1) count <;>
        simp [readNatList?, hcell, htailRead]

theorem readNatList?_append_two_at_end
    (heap : Heap) (base count : Nat) (xs : List Nat) (a b : Nat)
    (hread : readNatList? heap base count = some xs) :
    readNatList?
        (((heap.write (base + count) (.int (Int.ofNat a))).write
            (base + count + 1) (.int (Int.ofNat b))))
        base (count + 2) =
      some (xs ++ [a, b]) := by
  rw [readNatList?_append_two_at_end_map]
  simp [hread]

theorem readNatArray?_append_two_at_end
    (heap : Heap) (base count : Nat) (xs : Array Nat) (a b : Nat)
    (hread : readNatArray? heap base count = some xs) :
    readNatArray?
        (((heap.write (base + count) (.int (Int.ofNat a))).write
            (base + count + 1) (.int (Int.ofNat b))))
        base (count + 2) =
      some ((xs.push a).push b) := by
  cases hlist : readNatList? heap base count with
  | none =>
      simp [readNatArray?, hlist] at hread
  | some ys =>
      have hxs : ys.toArray = xs := by
        simp [readNatArray?, hlist] at hread
        exact hread
      rw [readNatArray?, readNatList?_append_two_at_end_map]
      simp [hlist]
      calc
        (ys ++ [a, b]).toArray = (ys.toArray.push a).push b := by
          simpa using array_toArray_append_two_eq_push_push ys.toArray a b
        _ = (xs.push a).push b := by
          simpa [hxs]

theorem readNatArray?_append_one_at_end
    (heap : Heap) (base count : Nat) (xs : Array Nat) (a : Nat)
    (hread : readNatArray? heap base count = some xs) :
    readNatArray?
        (heap.write (base + count) (.int (Int.ofNat a)))
        base (count + 1) =
      some (xs.push a) := by
  cases hlist : readNatList? heap base count with
  | none =>
      simp [readNatArray?, hlist] at hread
  | some ys =>
      have hxs : ys.toArray = xs := by
        simp [readNatArray?, hlist] at hread
        exact hread
      rw [readNatArray?, readNatList?_append_one_at_end_map]
      simp [hlist]
      calc
        (ys ++ [a]).toArray = ys.toArray.push a := by
          simpa using array_toArray_append_one_eq_push ys.toArray a
        _ = xs.push a := by
          simpa [hxs]

theorem readNatArray?_append_three_at_end
    (heap : Heap) (base count : Nat) (xs : Array Nat) (a b c : Nat)
    (hread : readNatArray? heap base count = some xs) :
    readNatArray?
        ((((heap.write (base + count) (.int (Int.ofNat a))).write
            (base + count + 1) (.int (Int.ofNat b))).write
            (base + count + 2) (.int (Int.ofNat c))))
        base (count + 3) =
      some (((xs.push a).push b).push c) := by
  have htwo :
      readNatArray?
          (((heap.write (base + count) (.int (Int.ofNat a))).write
              (base + count + 1) (.int (Int.ofNat b))))
          base (count + 2) =
        some ((xs.push a).push b) := by
    exact readNatArray?_append_two_at_end heap base count xs a b hread
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (readNatArray?_append_one_at_end
      (heap := (((heap.write (base + count) (.int (Int.ofNat a))).write
        (base + count + 1) (.int (Int.ofNat b)))))
      (base := base) (count := count + 2) (xs := (xs.push a).push b) (a := c) htwo)

theorem readFocus_encodeHeapWithLayout (s : State) (oracleVals : Array Int) :
    readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
      (layoutForState s oracleVals).focusBase = some s.focus := by
  simp only [encodeHeapWithLayout, encodeStackWithLayout, layoutForState, layoutFor]
  rw [readNatCell?_write_other _ _ _ _ (by omega)]
  rw [readNatCell?_write_other _ _ _ _ (by omega)]
  simpa using
    (readNatCell?_write_same
      (encodeStackWithLayout
        { tagsBase := 0
          lhsBase := s.maxNodes
          rhsBase := s.maxNodes + s.maxNodes
          refsBase := s.maxNodes + s.maxNodes + s.maxNodes
          oracleValsBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes
          stackBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals
          focusBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1)
          stackSizeBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1
          nodeCountBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1 }
        s oracleVals)
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
      s.focus)

theorem readStackSize_encodeHeapWithLayout (s : State) (oracleVals : Array Int) :
    readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
      (layoutForState s oracleVals).stackSizeBase = some s.stack.length := by
  simp only [encodeHeapWithLayout, encodeStackWithLayout, layoutForState, layoutFor]
  rw [readNatCell?_write_other _ _ _ _ (by omega)]
  simpa using
    (readNatCell?_write_same
      ((encodeStackWithLayout
          { tagsBase := 0
            lhsBase := s.maxNodes
            rhsBase := s.maxNodes + s.maxNodes
            refsBase := s.maxNodes + s.maxNodes + s.maxNodes
            oracleValsBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes
            stackBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals
            focusBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1)
            stackSizeBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1
            nodeCountBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1 }
          s oracleVals).write
        (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
        (.int (Int.ofNat s.focus)))
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
      s.stack.length)

theorem readNodeCount_encodeHeapWithLayout (s : State) (oracleVals : Array Int) :
    readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
      (layoutForState s oracleVals).nodeCountBase = some s.nodeCount := by
  simpa [encodeHeapWithLayout, encodeStackWithLayout, layoutForState, layoutFor] using
    (readNatCell?_write_same
      (((encodeStackWithLayout
            { tagsBase := 0
              lhsBase := s.maxNodes
              rhsBase := s.maxNodes + s.maxNodes
              refsBase := s.maxNodes + s.maxNodes + s.maxNodes
              oracleValsBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes
              stackBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals
              focusBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1)
              stackSizeBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1
              nodeCountBase := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1 }
            s oracleVals).write
          (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
          (.int (Int.ofNat s.focus))).write
        (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
        (.int (Int.ofNat s.stack.length)))
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1)
      s.nodeCount)

theorem readFocus_skyReducerScalarsLoadedState
    (s : State) (oracleVals : Array Int) :
    readNatCell? (skyReducerScalarsLoadedState s oracleVals).heap
      (layoutForState s oracleVals).focusBase = some s.focus := by
  rw [skyReducerScalarsLoadedState_heap_eq_encodeHeapWithLayout]
  simpa using readFocus_encodeHeapWithLayout s oracleVals

theorem readStackSize_skyReducerScalarsLoadedState
    (s : State) (oracleVals : Array Int) :
    readNatCell? (skyReducerScalarsLoadedState s oracleVals).heap
      (layoutForState s oracleVals).stackSizeBase = some s.stack.length := by
  rw [skyReducerScalarsLoadedState_heap_eq_encodeHeapWithLayout]
  simpa using readStackSize_encodeHeapWithLayout s oracleVals

theorem readNodeCount_skyReducerScalarsLoadedState
    (s : State) (oracleVals : Array Int) :
    readNatCell? (skyReducerScalarsLoadedState s oracleVals).heap
      (layoutForState s oracleVals).nodeCountBase = some s.nodeCount := by
  rw [skyReducerScalarsLoadedState_heap_eq_encodeHeapWithLayout]
  simpa using readNodeCount_encodeHeapWithLayout s oracleVals

def skyReducerScalarsCommittedState (s : State) (oracleVals : Array Int) : CState :=
  let st := skyReducerScalarsLoadedState s oracleVals
  ((st.withHeap st.heap).withHeap st.heap).withHeap st.heap

theorem execStmt_haltedCommit_skyReducerScalarsLoaded
    (s : State) (oracleVals : Array Int) :
    execStmt 4 (SKYLowering.commitAndReturn .halted)
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (skyReducerScalarsCommittedState s oracleVals)) := by
  let st0 := skyReducerScalarsLoadedState s oracleVals
  let st1 := st0.withHeap st0.heap
  let st2 := st1.withHeap st0.heap
  let st3 := st2.withHeap st0.heap
  have hHeap1 : st1.heap = st0.heap := by
    simp [st1]
  have hHeap2 : st2.heap = st0.heap := by
    simp [st2, st1]
  have hst2 : st2 = st1.withHeap st1.heap := by
    simp [st2, st1, hHeap1]
  have hst3 : st3 = st2.withHeap st2.heap := by
    simp [st3, st2, st1, hHeap2]
  have hFocusRead :
      readNatCell? st0.heap (layoutForState s oracleVals).focusBase = some s.focus := by
    simpa [st0] using readFocus_skyReducerScalarsLoadedState s oracleVals
  have hFocus :
      execStmt 2 (SKYLowering.writeScalar "focusPtr" (.var "focus")) st0 =
        some (.normal st1) := by
    have hBase :=
      execStmt_writeScalar_block0_of_lookups 1 st0 "focusPtr" "focus"
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))
        (by
          simpa [st0] using skyReducerScalarsLoadedState_lookup_focusPtr s oracleVals)
        (by
          simpa [st0] using skyReducerScalarsLoadedState_lookup_focus s oracleVals)
    have hWrite :
        st0.heap.write (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus)) = st0.heap :=
      heap_write_eq_of_readNatCell_eq st0.heap (layoutForState s oracleVals).focusBase
        s.focus hFocusRead
    rw [hWrite] at hBase
    simpa [st0, st1] using hBase
  have hStackRead :
      readNatCell? st1.heap (layoutForState s oracleVals).stackSizeBase = some s.stack.length := by
    simpa [hHeap1] using readStackSize_skyReducerScalarsLoadedState s oracleVals
  have hStack :
      execStmt 2 (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize")) st1 =
        some (.normal st2) := by
    have hBase :=
      execStmt_writeScalar_block0_of_lookups 1 st1 "stackSizePtr" "stackSize"
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))
        (by
          simpa [st0, st1] using skyReducerScalarsLoadedState_lookup_stackSizePtr s oracleVals)
        (by
          simpa [st0, st1] using skyReducerScalarsLoadedState_lookup_stackSize s oracleVals)
    have hWrite :
        st1.heap.write (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length)) =
          st1.heap :=
      heap_write_eq_of_readNatCell_eq st1.heap (layoutForState s oracleVals).stackSizeBase
        s.stack.length hStackRead
    rw [hWrite] at hBase
    simpa [hst2] using hBase
  have hNodeRead :
      readNatCell? st2.heap (layoutForState s oracleVals).nodeCountBase = some s.nodeCount := by
    simpa [hHeap2] using readNodeCount_skyReducerScalarsLoadedState s oracleVals
  have hNode :
      execStmt 2 (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount")) st2 =
        some (.normal st3) := by
    have hBase :=
      execStmt_writeScalar_block0_of_lookups 1 st2 "nodeCountPtr" "nodeCount"
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))
        (by
          simpa [st0, st1, st2] using skyReducerScalarsLoadedState_lookup_nodeCountPtr s oracleVals)
        (by
          simpa [st0, st1, st2] using skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals)
    have hWrite :
        st2.heap.write (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount)) =
          st2.heap :=
      heap_write_eq_of_readNatCell_eq st2.heap (layoutForState s oracleVals).nodeCountBase
        s.nodeCount hNodeRead
    rw [hWrite] at hBase
    simpa [hst3] using hBase
  simpa [st0, st1, st2, st3, hHeap1, hHeap2, hst2, hst3] using
    (execStmt_commitAndReturn_of_steps .halted st0 st1 st2 st3 hFocus hStack hNode)

theorem readTags_encodeHeapWithLayout (s : State) (oracleVals : Array Int)
    (hnodes : s.nodeCount ≤ s.maxNodes) :
    readIntArray? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
      (layoutForState s oracleVals).tagsBase s.nodeCount = some s.tags := by
  simp only [encodeHeapWithLayout, encodeStackWithLayout, encodeOracleValuesWithLayout,
    encodeNodeArraysWithLayout, layoutForState, layoutFor, State.nodeCount] at *
  rw [readIntArray?_write_other _ _ _ 0 s.tags.size (Or.inr (by omega))]
  rw [readIntArray?_write_other _ _ _ 0 s.tags.size (Or.inr (by omega))]
  rw [readIntArray?_write_other _ _ _ 0 s.tags.size (Or.inr (by omega))]
  rw [readIntArray?_writeNatList_otherRange _ _ _ 0 s.tags.size (by omega)]
  rw [readIntArray?_writeIntList_otherRange _ _ _ 0 s.tags.size (by omega)]
  rw [readIntArray?_writeNatList_otherRange _ _ _ 0 s.tags.size (by omega)]
  rw [readIntArray?_writeNatList_otherRange _ _ _ 0 s.tags.size (by omega)]
  rw [readIntArray?_writeNatList_otherRange _ _ _ 0 s.tags.size (by omega)]
  simpa using (readIntArray?_writeIntList Heap.empty 0 s.tags.toList)

theorem readLhs_encodeHeapWithLayout (s : State) (oracleVals : Array Int)
    (hlhs : s.lhs.size = s.nodeCount) (hnodes : s.nodeCount ≤ s.maxNodes) :
    readNatArray? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
      (layoutForState s oracleVals).lhsBase s.nodeCount = some s.lhs := by
  simp only [encodeHeapWithLayout, encodeStackWithLayout, encodeOracleValuesWithLayout,
    encodeNodeArraysWithLayout, layoutForState, layoutFor, State.nodeCount] at *
  rw [readNatArray?_write_other _ _ _ (0 + s.maxNodes) s.tags.size (Or.inr (by omega))]
  rw [readNatArray?_write_other _ _ _ (0 + s.maxNodes) s.tags.size (Or.inr (by omega))]
  rw [readNatArray?_write_other _ _ _ (0 + s.maxNodes) s.tags.size (Or.inr (by omega))]
  rw [readNatArray?_writeNatList_otherRange _ _ _ (0 + s.maxNodes) s.tags.size (by omega)]
  rw [readNatArray?_writeIntList_otherRange _ _ _ (0 + s.maxNodes) s.tags.size (by omega)]
  rw [readNatArray?_writeNatList_otherRange _ _ _ (0 + s.maxNodes) s.tags.size (by omega)]
  rw [readNatArray?_writeNatList_otherRange _ _ _ (0 + s.maxNodes) s.tags.size (by omega)]
  rw [← hlhs]
  simpa using
    (readNatArray?_writeNatList (writeIntList Heap.empty 0 s.tags.toList) (0 + s.maxNodes) s.lhs.toList)

theorem readRhs_encodeHeapWithLayout (s : State) (oracleVals : Array Int)
    (hrhs : s.rhs.size = s.nodeCount) (hnodes : s.nodeCount ≤ s.maxNodes) :
    readNatArray? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
      (layoutForState s oracleVals).rhsBase s.nodeCount = some s.rhs := by
  simp only [encodeHeapWithLayout, encodeStackWithLayout, encodeOracleValuesWithLayout,
    encodeNodeArraysWithLayout, layoutForState, layoutFor, State.nodeCount] at *
  rw [readNatArray?_write_other _ _ _ (0 + s.maxNodes + s.maxNodes) s.tags.size (Or.inr (by omega))]
  rw [readNatArray?_write_other _ _ _ (0 + s.maxNodes + s.maxNodes) s.tags.size (Or.inr (by omega))]
  rw [readNatArray?_write_other _ _ _ (0 + s.maxNodes + s.maxNodes) s.tags.size (Or.inr (by omega))]
  rw [readNatArray?_writeNatList_otherRange _ _ _ (0 + s.maxNodes + s.maxNodes) s.tags.size (by omega)]
  rw [readNatArray?_writeIntList_otherRange _ _ _ (0 + s.maxNodes + s.maxNodes) s.tags.size (by omega)]
  rw [readNatArray?_writeNatList_otherRange _ _ _ (0 + s.maxNodes + s.maxNodes) s.tags.size (by omega)]
  rw [← hrhs]
  simpa [Nat.add_assoc] using
    (readNatArray?_writeNatList
      (writeNatList (writeIntList Heap.empty 0 s.tags.toList) (0 + s.maxNodes) s.lhs.toList)
      (0 + s.maxNodes + s.maxNodes) s.rhs.toList)

theorem readOracleRefs_encodeHeapWithLayout (s : State) (oracleVals : Array Int)
    (hrefs : s.oracleRefs.size = s.nodeCount) (hnodes : s.nodeCount ≤ s.maxNodes) :
    readNatArray? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
      (layoutForState s oracleVals).refsBase s.nodeCount = some s.oracleRefs := by
  simp only [encodeHeapWithLayout, encodeStackWithLayout, encodeOracleValuesWithLayout,
    encodeNodeArraysWithLayout, layoutForState, layoutFor, State.nodeCount] at *
  rw [readNatArray?_write_other _ _ _ (0 + s.maxNodes + s.maxNodes + s.maxNodes) s.tags.size
    (Or.inr (by omega))]
  rw [readNatArray?_write_other _ _ _ (0 + s.maxNodes + s.maxNodes + s.maxNodes) s.tags.size
    (Or.inr (by omega))]
  rw [readNatArray?_write_other _ _ _ (0 + s.maxNodes + s.maxNodes + s.maxNodes) s.tags.size
    (Or.inr (by omega))]
  rw [readNatArray?_writeNatList_otherRange _ _ _ (0 + s.maxNodes + s.maxNodes + s.maxNodes)
    s.tags.size (by omega)]
  rw [readNatArray?_writeIntList_otherRange _ _ _ (0 + s.maxNodes + s.maxNodes + s.maxNodes)
    s.tags.size (by omega)]
  rw [← hrefs]
  simpa [Nat.add_assoc] using
    (readNatArray?_writeNatList
      (writeNatList
        (writeNatList (writeIntList Heap.empty 0 s.tags.toList) (0 + s.maxNodes) s.lhs.toList)
        (0 + s.maxNodes + s.maxNodes) s.rhs.toList)
      (0 + s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList)

theorem readStack_encodeHeapWithLayout (s : State) (oracleVals : Array Int) :
    readNatArray? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
      (layoutForState s oracleVals).stackBase s.stack.length = some s.stack.reverse.toArray := by
  simp only [encodeHeapWithLayout, encodeStackWithLayout, encodeOracleValuesWithLayout,
    encodeNodeArraysWithLayout, layoutForState, layoutFor]
  rw [readNatArray?_write_other _ _ _
    (0 + s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals)
    s.stack.length (Or.inr (by omega))]
  rw [readNatArray?_write_other _ _ _
    (0 + s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals)
    s.stack.length (Or.inr (by omega))]
  rw [readNatArray?_write_other _ _ _
    (0 + s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals)
    s.stack.length (Or.inr (by omega))]
  simpa [Nat.add_assoc] using
    (readNatArray?_writeNatList
      (writeIntList
        (writeNatList
          (writeNatList
            (writeNatList (writeIntList Heap.empty 0 s.tags.toList) (0 + s.maxNodes) s.lhs.toList)
            (0 + s.maxNodes + s.maxNodes) s.rhs.toList)
          (0 + s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList)
        (0 + s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes) (oracleValuesPadded s oracleVals))
      (0 + s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals) s.stack.reverse)

theorem heap_write_comm (heap : Heap) (addr₁ addr₂ : Nat) (v₁ v₂ : CVal)
    (hneq : addr₁ ≠ addr₂) :
    (heap.write addr₁ v₁).write addr₂ v₂ = (heap.write addr₂ v₂).write addr₁ v₁ := by
  apply Finmap.ext_lookup
  intro addr
  by_cases h1 : addr = addr₁
  · subst h1
    simp [Heap.write, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, hneq]
  · by_cases h2 : addr = addr₂
    · subst h2
      simp [Heap.write, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, hneq, hneq.symm]
    · simp [Heap.write, Finmap.lookup_insert_of_ne, h1, h2]

theorem readFocus_skyReducerAppCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    readNatCell? (skyReducerAppCommittedState s oracleVals hwf hfocus).heap
      (layoutForState s oracleVals).focusBase =
        some (s.lhs[s.focus]'(by
          rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
          simpa [hlhs] using hfocus)) := by
  have hFocusNeNodeCountBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hFocusNeStackSizeBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerAppCommittedState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerAppCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeNodeCountBase]
  rw [show (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length + 1)))) by
      simp [skyReducerAppCommittedStackSizeState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeStackSizeBase]
  simpa [skyReducerAppCommittedFocusState, skyReducerAppFocusVal]
    using (readNatCell?_write_same
      (heap := (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap)
      (addr := (layoutForState s oracleVals).focusBase)
      (n := s.lhs[s.focus]'(by
        rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
        simpa [hlhs] using hfocus)))

theorem readStackSize_skyReducerAppCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    readNatCell? (skyReducerAppCommittedState s oracleVals hwf hfocus).heap
      (layoutForState s oracleVals).stackSizeBase = some (s.stack.length + 1) := by
  have hStackSizeNeNodeCountBase :
      (layoutForState s oracleVals).stackSizeBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerAppCommittedState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerAppCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hStackSizeNeNodeCountBase]
  simpa [skyReducerAppCommittedStackSizeState]
    using (readNatCell?_write_same
      (heap := (skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap)
      (addr := (layoutForState s oracleVals).stackSizeBase)
      (n := s.stack.length + 1))

theorem readNodeCount_skyReducerAppCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    readNatCell? (skyReducerAppCommittedState s oracleVals hwf hfocus).heap
      (layoutForState s oracleVals).nodeCountBase = some s.nodeCount := by
  simpa [skyReducerAppCommittedState]
    using (readNatCell?_write_same
      (heap := (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap)
      (addr := (layoutForState s oracleVals).nodeCountBase)
      (n := s.nodeCount))

theorem readTags_skyReducerAppCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    readIntArray? (skyReducerAppCommittedState s oracleVals hwf hfocus).heap
      (layoutForState s oracleVals).tagsBase s.nodeCount = some s.tags := by
  have hwf' := hwf
  rcases hwf' with ⟨_hlhs, _hrhs, _hrefs, hnodes, _hstack⟩
  have hTagsNodeCount :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsStackSize :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsFocus :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsAppend :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackBase + s.stack.length := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerAppCommittedState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerAppCommittedState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsNodeCount)]
  rw [show (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length + 1)))) by
      simp [skyReducerAppCommittedStackSizeState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsStackSize)]
  rw [show (skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap =
      (((skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).focusBase (skyReducerAppFocusVal s hwf hfocus)) by
      simp [skyReducerAppCommittedFocusState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsFocus)]
  rw [show (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap =
      ((skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.write
        ((layoutForState s oracleVals).stackBase + s.stack.length)
        (skyReducerAppXVal s hwf hfocus)) by
      simp [skyReducerAppStackSizeUpdatedState, skyReducerAppFocusUpdatedState, skyReducerAppStoredState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsAppend)]
  simpa [skyReducerAppXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
    skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
    encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap]
    using readTags_encodeHeapWithLayout s oracleVals hnodes

theorem readLhs_skyReducerAppCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    readNatArray? (skyReducerAppCommittedState s oracleVals hwf hfocus).heap
      (layoutForState s oracleVals).lhsBase s.nodeCount = some s.lhs := by
  have hwf' := hwf
  rcases hwf' with ⟨hlhs, _hrhs, _hrefs, hnodes, _hstack⟩
  have hLhsNodeCount :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsStackSize :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsFocus :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsAppend :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackBase + s.stack.length := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerAppCommittedState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerAppCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsNodeCount)]
  rw [show (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length + 1)))) by
      simp [skyReducerAppCommittedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsStackSize)]
  rw [show (skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap =
      (((skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).focusBase (skyReducerAppFocusVal s hwf hfocus)) by
      simp [skyReducerAppCommittedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsFocus)]
  rw [show (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap =
      ((skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.write
        ((layoutForState s oracleVals).stackBase + s.stack.length)
        (skyReducerAppXVal s hwf hfocus)) by
      simp [skyReducerAppStackSizeUpdatedState, skyReducerAppFocusUpdatedState, skyReducerAppStoredState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsAppend)]
  simpa [skyReducerAppXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
    skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
    encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap]
    using readLhs_encodeHeapWithLayout s oracleVals hlhs hnodes

theorem readRhs_skyReducerAppCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    readNatArray? (skyReducerAppCommittedState s oracleVals hwf hfocus).heap
      (layoutForState s oracleVals).rhsBase s.nodeCount = some s.rhs := by
  have hwf' := hwf
  rcases hwf' with ⟨_hlhs, hrhs, _hrefs, hnodes, _hstack⟩
  have hRhsNodeCount :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsStackSize :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsFocus :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsAppend :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackBase + s.stack.length := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerAppCommittedState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerAppCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsNodeCount)]
  rw [show (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length + 1)))) by
      simp [skyReducerAppCommittedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsStackSize)]
  rw [show (skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap =
      (((skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).focusBase (skyReducerAppFocusVal s hwf hfocus)) by
      simp [skyReducerAppCommittedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsFocus)]
  rw [show (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap =
      ((skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.write
        ((layoutForState s oracleVals).stackBase + s.stack.length)
        (skyReducerAppXVal s hwf hfocus)) by
      simp [skyReducerAppStackSizeUpdatedState, skyReducerAppFocusUpdatedState, skyReducerAppStoredState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsAppend)]
  simpa [skyReducerAppXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
    skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
    encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap]
    using readRhs_encodeHeapWithLayout s oracleVals hrhs hnodes

theorem readOracleRefs_skyReducerAppCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    readNatArray? (skyReducerAppCommittedState s oracleVals hwf hfocus).heap
      (layoutForState s oracleVals).refsBase s.nodeCount = some s.oracleRefs := by
  have hwf' := hwf
  rcases hwf' with ⟨_hlhs, _hrhs, hrefs, hnodes, _hstack⟩
  have hRefsNodeCount :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsStackSize :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsFocus :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsAppend :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackBase + s.stack.length := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerAppCommittedState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerAppCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsNodeCount)]
  rw [show (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length + 1)))) by
      simp [skyReducerAppCommittedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsStackSize)]
  rw [show (skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap =
      (((skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap).write
        (layoutForState s oracleVals).focusBase (skyReducerAppFocusVal s hwf hfocus)) by
      simp [skyReducerAppCommittedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsFocus)]
  rw [show (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap =
      ((skyReducerAppXLoadedState s oracleVals hwf hfocus).heap.write
        ((layoutForState s oracleVals).stackBase + s.stack.length)
        (skyReducerAppXVal s hwf hfocus)) by
      simp [skyReducerAppStackSizeUpdatedState, skyReducerAppFocusUpdatedState, skyReducerAppStoredState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsAppend)]
  simpa [skyReducerAppXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
    skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
    encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap]
    using readOracleRefs_encodeHeapWithLayout s oracleVals hrefs hnodes

theorem readStack_skyReducerAppCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    readNatArray? (skyReducerAppCommittedState s oracleVals hwf hfocus).heap
      (layoutForState s oracleVals).stackBase (s.stack.length + 1) =
        some ((s.stack.reverse ++
          [s.rhs[s.focus]'(by
            rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
            simpa [hrhs] using hfocus)]).toArray) := by
  let layout := layoutForState s oracleVals
  let xNat := s.rhs[s.focus]'(by
    rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
    simpa [hrhs] using hfocus)
  have hRangeNodeCount : layout.stackBase + (s.stack.length + 1) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRangeStackSize : layout.stackBase + (s.stack.length + 1) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
  have hRangeFocus : layout.stackBase + (s.stack.length + 1) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
  have hAppendNeNodeCount : layout.stackBase + s.stack.length ≠ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hAppendNeStackSize : layout.stackBase + s.stack.length ≠ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hAppendNeFocus : layout.stackBase + s.stack.length ≠ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
  rw [show (skyReducerAppCommittedState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap).write
        layout.nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerAppCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRangeNodeCount)]
  rw [show (skyReducerAppCommittedStackSizeState s oracleVals hwf hfocus).heap =
      (((skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length + 1)))) by
      simp [skyReducerAppCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRangeStackSize)]
  rw [show (skyReducerAppCommittedFocusState s oracleVals hwf hfocus).heap =
      (((skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap).write
        layout.focusBase (skyReducerAppFocusVal s hwf hfocus)) by
      simp [skyReducerAppCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRangeFocus)]
  rw [show (skyReducerAppStackSizeUpdatedState s oracleVals hwf hfocus).heap =
      ((encodeHeapWithLayout layout s oracleVals).write
        (layout.stackBase + s.stack.length) (skyReducerAppXVal s hwf hfocus)) by
      simp [skyReducerAppStackSizeUpdatedState, skyReducerAppFocusUpdatedState,
        skyReducerAppStoredState, skyReducerAppXLoadedState, skyReducerAppTagLoadedState,
        skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
        skyReducerEntry, encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap, layout]]
  simp only [encodeHeapWithLayout]
  rw [show
      ((((encodeStackWithLayout layout s oracleVals).write layout.focusBase (.int (Int.ofNat s.focus))).write
            layout.stackSizeBase (.int (Int.ofNat s.stack.length))).write
          layout.nodeCountBase (.int (Int.ofNat s.nodeCount))).write
        (layout.stackBase + s.stack.length) (skyReducerAppXVal s hwf hfocus)
      =
      ((((encodeStackWithLayout layout s oracleVals).write layout.focusBase (.int (Int.ofNat s.focus))).write
            layout.stackSizeBase (.int (Int.ofNat s.stack.length))).write
          (layout.stackBase + s.stack.length) (skyReducerAppXVal s hwf hfocus)).write
        layout.nodeCountBase (.int (Int.ofNat s.nodeCount)) by
      simpa using
        (heap_write_comm
          (heap := ((encodeStackWithLayout layout s oracleVals).write
              layout.focusBase (.int (Int.ofNat s.focus))).write
              layout.stackSizeBase (.int (Int.ofNat s.stack.length)))
          (addr₁ := layout.nodeCountBase)
          (addr₂ := layout.stackBase + s.stack.length)
          (v₁ := .int (Int.ofNat s.nodeCount))
          (v₂ := skyReducerAppXVal s hwf hfocus)
          hAppendNeNodeCount.symm)]
  rw [heap_write_comm
      (heap := (encodeStackWithLayout layout s oracleVals).write
        layout.focusBase (.int (Int.ofNat s.focus)))
      (addr₁ := layout.stackSizeBase)
      (addr₂ := layout.stackBase + s.stack.length)
      (v₁ := .int (Int.ofNat s.stack.length))
      (v₂ := skyReducerAppXVal s hwf hfocus)
      hAppendNeStackSize.symm]
  rw [heap_write_comm
      (heap := encodeStackWithLayout layout s oracleVals)
      (addr₁ := layout.focusBase)
      (addr₂ := layout.stackBase + s.stack.length)
      (v₁ := .int (Int.ofNat s.focus))
      (v₂ := skyReducerAppXVal s hwf hfocus)
      hAppendNeFocus.symm]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRangeNodeCount)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRangeStackSize)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRangeFocus)]
  simp [encodeStackWithLayout]
  have hxVal : skyReducerAppXVal s hwf hfocus = .int (Int.ofNat xNat) := by
    simp [skyReducerAppXVal, xNat]
  rw [hxVal]
  calc
    readNatArray?
        ((writeNatList (encodeOracleValuesWithLayout layout s oracleVals) layout.stackBase s.stack.reverse).write
          (layout.stackBase + s.stack.length) (.int (Int.ofNat xNat)))
        layout.stackBase (s.stack.length + 1)
        =
      readNatArray?
        (writeNatList
          (writeNatList (encodeOracleValuesWithLayout layout s oracleVals) layout.stackBase s.stack.reverse)
          (layout.stackBase + s.stack.length) [xNat])
        layout.stackBase (s.stack.length + 1) := by
          simp [writeNatList]
    _ =
      readNatArray?
        (writeNatList (encodeOracleValuesWithLayout layout s oracleVals) layout.stackBase
          (s.stack.reverse ++ [xNat]))
        layout.stackBase (s.stack.length + 1) := by
          simp [writeNatList_append, layout, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = some ((s.stack.reverse ++ [xNat]).toArray) := by
          simpa [xNat, layout] using
            (readNatArray?_writeNatList
              (heap := encodeOracleValuesWithLayout layout s oracleVals)
              (base := layout.stackBase)
              (xs := s.stack.reverse ++ [xNat]))
    _ = some ((s.stack.reverse ++
          [s.rhs[s.focus]'(by
            rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
            simpa [hrhs] using hfocus)]).toArray) := by
          simp [xNat]

theorem decodeKernelState?_skyReducerAppCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (skyReducerAppCommittedState s oracleVals hwf hfocus) =
        some { s with
          focus := s.lhs[s.focus]'(by
            rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
            simpa [hlhs] using hfocus)
          stack := s.rhs[s.focus]'(by
            rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
            simpa [hrhs] using hfocus) :: s.stack } := by
  rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, _hstack⟩
  simp [decodeKernelState?,
    readFocus_skyReducerAppCommittedState, readStackSize_skyReducerAppCommittedState,
    readNodeCount_skyReducerAppCommittedState, readTags_skyReducerAppCommittedState,
    readLhs_skyReducerAppCommittedState, readRhs_skyReducerAppCommittedState,
    readOracleRefs_skyReducerAppCommittedState, readStack_skyReducerAppCommittedState,
    hlhs, hrhs, hrefs, hnodes]

theorem runLoweredStep?_app
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app) :
    runLoweredStep? s oracleVals =
      some (.progress, { s with
        focus := s.lhs[s.focus]'(by
          rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
          simpa [hlhs] using hfocus)
        stack := s.rhs[s.focus]'(by
          rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
          simpa [hrhs] using hfocus) :: s.stack }) := by
  simp [runLoweredStep?]
  rw [execStmt_appPath_encodeExecState_runLoweredBudget s oracleVals hwf hfocus happ]
  simp [StepStatus.ofCode?, StepStatus.code]
  rw [decodeKernelState?_skyReducerAppCommittedState]
  simp [StepStatus.ofCode?, StepStatus.code]

theorem readFocus_skyReducerYCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    readNatCell? (skyReducerYCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).focusBase = some (skyReducerYOutNat s) := by
  have hFocusNeNodeCountBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hFocusNeStackSizeBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerYCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat (s.nodeCount + 2)))) by
      simp [skyReducerYCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeNodeCountBase]
  rw [show (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 1)))) by
      simp [skyReducerYCommittedStackSizeState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeStackSizeBase]
  simpa [skyReducerYCommittedFocusState, skyReducerYOutVal, skyReducerYOutNat]
    using (readNatCell?_write_same
      (heap := (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap)
      (addr := (layoutForState s oracleVals).focusBase)
      (n := skyReducerYOutNat s))

theorem readStackSize_skyReducerYCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    readNatCell? (skyReducerYCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).stackSizeBase = some (s.stack.length - 1) := by
  have hStackSizeNeNodeCountBase :
      (layoutForState s oracleVals).stackSizeBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerYCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat (s.nodeCount + 2)))) by
      simp [skyReducerYCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hStackSizeNeNodeCountBase]
  simpa [skyReducerYCommittedStackSizeState]
    using (readNatCell?_write_same
      (heap := (skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap)
      (addr := (layoutForState s oracleVals).stackSizeBase)
      (n := s.stack.length - 1))

theorem readNodeCount_skyReducerYCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) :
    readNatCell? (skyReducerYCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).nodeCountBase = some (s.nodeCount + 2) := by
  simpa [skyReducerYCommittedState]
    using (readNatCell?_write_same
      (heap := (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap)
      (addr := (layoutForState s oracleVals).nodeCountBase)
      (n := s.nodeCount + 2))

theorem readTags_skyReducerYCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes) :
    readIntArray? (skyReducerYCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).tagsBase (s.nodeCount + 2) =
        some ((s.tags.push (NodeTag.code .app)).push (NodeTag.code .app)) := by
  let layout := layoutForState s oracleVals
  have hTagsNodeCount :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsStackSize :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsFocus :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsLhs :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.lhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsLhsOut :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.lhsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRhs :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.rhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRhsOut :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.rhsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRefs :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.refsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRefsOut :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.refsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerYCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 2)))) by
      simp [skyReducerYCommittedState, layout]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsNodeCount)]
  rw [show (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 1)))) by
      simp [skyReducerYCommittedStackSizeState, layout]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsStackSize)]
  rw [show (skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerYOutVal s)) by
      simp [skyReducerYCommittedFocusState, layout]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsFocus)]
  rw [show (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerYStackSizeUpdatedState, skyReducerYNodeCountUpdatedState,
        skyReducerYFocusUpdatedState]]
  rw [show (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 1) (.int 0)) by
      simp [skyReducerYOutRefStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRefsOut)]
  rw [show (skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)) by
      simp [skyReducerYOutRhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRhsOut)]
  rw [show (skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)) by
      simp [skyReducerYOutLhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsLhsOut)]
  rw [show (skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
      simp [skyReducerYOutTagStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount) (.int 0)) by
      simp [skyReducerYSelfRefStoredState, layout, skyReducerYSelfNat]]
  have hTagsSelfRefNe :
      layout.refsBase + s.nodeCount ≠ layout.tagsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show
      ((((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)).write
          (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app)) =
        ((((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))).write
          (layout.refsBase + s.nodeCount) (.int 0))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.refsBase + s.nodeCount)
          (addr₂ := layout.tagsBase + s.nodeCount + 1)
          (v₁ := .int 0)
          (v₂ := .int (NodeTag.code .app))
          hTagsSelfRefNe)]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRefs)]
  rw [show (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)) by
      simp [skyReducerYSelfRhsStoredState, layout, skyReducerYSelfNat]]
  have hTagsSelfRhsNe :
      layout.rhsBase + s.nodeCount ≠ layout.tagsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show
      ((((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
          (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app)) =
        ((((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))).write
          (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.rhsBase + s.nodeCount)
          (addr₂ := layout.tagsBase + s.nodeCount + 1)
          (v₁ := skyReducerYXVal s hstack)
          (v₂ := .int (NodeTag.code .app))
          hTagsSelfRhsNe)]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRhs)]
  rw [show (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))) by
      simp [skyReducerYSelfLhsStoredState, layout, skyReducerYSelfNat]]
  have hTagsSelfLhsNe :
      layout.lhsBase + s.nodeCount ≠ layout.tagsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show
      ((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))).write
          (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app)) =
        ((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))).write
          (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus)))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.lhsBase + s.nodeCount)
          (addr₂ := layout.tagsBase + s.nodeCount + 1)
          (v₁ := .int (Int.ofNat s.focus))
          (v₂ := .int (NodeTag.code .app))
          hTagsSelfLhsNe)]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsLhs)]
  rw [show (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
      simp [skyReducerYSelfTagStoredState, layout, skyReducerYSelfNat]]
  rw [show (skyReducerYXLoadedState s oracleVals hfocus hstack).heap =
      encodeHeapWithLayout layout s oracleVals by
      simp [skyReducerYXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
        skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
        encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap, layout]]
  have hTagsBaseRead :
      readIntArray? (encodeHeapWithLayout layout s oracleVals) layout.tagsBase s.nodeCount =
        some s.tags := by
    simpa [layout] using readTags_encodeHeapWithLayout s oracleVals (by omega)
  simpa [layout] using
    (readIntArray?_append_two_at_end
      (heap := encodeHeapWithLayout layout s oracleVals)
      (base := layout.tagsBase)
      (count := s.nodeCount)
      (xs := s.tags)
      (a := NodeTag.code .app)
      (b := NodeTag.code .app)
      hTagsBaseRead)

theorem readLhs_skyReducerYCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes) :
    readNatArray? (skyReducerYCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).lhsBase (s.nodeCount + 2) =
        some ((s.lhs.push s.focus).push
          (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hstack⟩)) := by
  rcases hwf with ⟨hlhs, _hrhs, _hrefs, hnodes, _hstackBound⟩
  let layout := layoutForState s oracleVals
  let xNat := s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hstack⟩
  have hLhsNodeCount :
      layout.lhsBase + (s.nodeCount + 2) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsStackSize :
      layout.lhsBase + (s.nodeCount + 2) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsFocus :
      layout.lhsBase + (s.nodeCount + 2) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRhs :
      layout.lhsBase + (s.nodeCount + 2) ≤ layout.rhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRhsOut :
      layout.lhsBase + (s.nodeCount + 2) ≤ layout.rhsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRefs :
      layout.lhsBase + (s.nodeCount + 2) ≤ layout.refsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRefsOut :
      layout.lhsBase + (s.nodeCount + 2) ≤ layout.refsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagSelfBefore :
      layout.tagsBase + s.nodeCount < layout.lhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagOutBefore :
      layout.tagsBase + s.nodeCount + 1 < layout.lhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsOutTagOutNe :
      layout.lhsBase + s.nodeCount + 1 ≠ layout.tagsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsOutRefNe :
      layout.lhsBase + s.nodeCount + 1 ≠ layout.refsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsOutRhsNe :
      layout.lhsBase + s.nodeCount + 1 ≠ layout.rhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsSelfTagSelfNe :
      layout.lhsBase + s.nodeCount ≠ layout.tagsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsOutTagSelfNe :
      layout.lhsBase + s.nodeCount + 1 ≠ layout.tagsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerYCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 2)))) by
      simp [skyReducerYCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsNodeCount)]
  rw [show (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 1)))) by
      simp [skyReducerYCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsStackSize)]
  rw [show (skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerYOutVal s)) by
      simp [skyReducerYCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsFocus)]
  rw [show (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerYStackSizeUpdatedState, skyReducerYNodeCountUpdatedState,
        skyReducerYFocusUpdatedState]]
  rw [show (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 1) (.int 0)) by
      simp [skyReducerYOutRefStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRefsOut)]
  rw [show (skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)) by
      simp [skyReducerYOutRhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRhsOut)]
  rw [show (skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)) by
      simp [skyReducerYOutLhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show (skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
      simp [skyReducerYOutTagStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show
      ((((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))).write
          (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack) =
        ((((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)).write
          (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app)))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.tagsBase + s.nodeCount + 1)
          (addr₂ := layout.lhsBase + s.nodeCount + 1)
          (v₁ := .int (NodeTag.code .app))
          (v₂ := skyReducerYXVal s hstack)
          hLhsOutTagOutNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTagOutBefore)]
  rw [show (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount) (.int 0)) by
      simp [skyReducerYSelfRefStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)).write
          (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack) =
        ((((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)).write
          (layout.refsBase + s.nodeCount) (.int 0))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.refsBase + s.nodeCount)
          (addr₂ := layout.lhsBase + s.nodeCount + 1)
          (v₁ := .int 0)
          (v₂ := skyReducerYXVal s hstack)
          hLhsOutRefNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRefs)]
  rw [show (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)) by
      simp [skyReducerYSelfRhsStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
          (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack) =
        ((((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)).write
          (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.rhsBase + s.nodeCount)
          (addr₂ := layout.lhsBase + s.nodeCount + 1)
          (v₁ := skyReducerYXVal s hstack)
          (v₂ := skyReducerYXVal s hstack)
          hLhsOutRhsNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRhs)]
  rw [show (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))) by
      simp [skyReducerYSelfLhsStoredState, layout, skyReducerYSelfNat]]
  rw [show (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
      simp [skyReducerYSelfTagStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))).write
          (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus)) =
        ((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))).write
          (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app)))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYXLoadedState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.tagsBase + s.nodeCount)
          (addr₂ := layout.lhsBase + s.nodeCount)
          (v₁ := .int (NodeTag.code .app))
          (v₂ := .int (Int.ofNat s.focus))
          hLhsSelfTagSelfNe.symm)]
  rw [show
      (((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
              (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))).write
            (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))).write
          (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack) =
        (((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
              (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))).write
            (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)).write
          (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app)))) by
      simpa using
        (heap_write_comm
          (heap := (((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))))
          (addr₁ := layout.tagsBase + s.nodeCount)
          (addr₂ := layout.lhsBase + s.nodeCount + 1)
          (v₁ := .int (NodeTag.code .app))
          (v₂ := skyReducerYXVal s hstack)
          hLhsOutTagSelfNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTagSelfBefore)]
  rw [show (skyReducerYXLoadedState s oracleVals hfocus hstack).heap =
      encodeHeapWithLayout layout s oracleVals by
      simp [skyReducerYXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
        skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
        encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap, layout]]
  have hLhsBaseRead :
      readNatArray? (encodeHeapWithLayout layout s oracleVals) layout.lhsBase s.nodeCount =
        some s.lhs := by
    simpa [layout, hlhs] using readLhs_encodeHeapWithLayout s oracleVals hlhs hnodes
  have hxVal : skyReducerYXVal s hstack = .int (Int.ofNat xNat) := by
    simp [skyReducerYXVal, xNat]
  rw [hxVal]
  simpa [layout, xNat] using
    (readNatArray?_append_two_at_end
      (heap := encodeHeapWithLayout layout s oracleVals)
      (base := layout.lhsBase)
      (count := s.nodeCount)
      (xs := s.lhs)
      (a := s.focus)
      (b := xNat)
      hLhsBaseRead)

theorem readRhs_skyReducerYCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes) :
    readNatArray? (skyReducerYCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).rhsBase (s.nodeCount + 2) =
        some ((s.rhs.push
          (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hstack⟩)).push s.nodeCount) := by
  rcases hwf with ⟨_hlhs, hrhs, _hrefs, hnodes, _hstackBound⟩
  let layout := layoutForState s oracleVals
  let xNat := s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hstack⟩
  have hRhsNodeCount :
      layout.rhsBase + (s.nodeCount + 2) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsStackSize :
      layout.rhsBase + (s.nodeCount + 2) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsFocus :
      layout.rhsBase + (s.nodeCount + 2) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsRefs :
      layout.rhsBase + (s.nodeCount + 2) ≤ layout.refsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsRefsOut :
      layout.rhsBase + (s.nodeCount + 2) ≤ layout.refsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsSelfBefore :
      layout.lhsBase + s.nodeCount < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsOutBefore :
      layout.lhsBase + s.nodeCount + 1 < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagSelfBefore :
      layout.tagsBase + s.nodeCount < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagOutBefore :
      layout.tagsBase + s.nodeCount + 1 < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsOutLhsOutNe :
      layout.rhsBase + s.nodeCount + 1 ≠ layout.lhsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsOutTagOutNe :
      layout.rhsBase + s.nodeCount + 1 ≠ layout.tagsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsOutRefNe :
      layout.rhsBase + s.nodeCount + 1 ≠ layout.refsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsSelfLhsSelfNe :
      layout.rhsBase + s.nodeCount ≠ layout.lhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsOutLhsSelfNe :
      layout.rhsBase + s.nodeCount + 1 ≠ layout.lhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsSelfTagSelfNe :
      layout.rhsBase + s.nodeCount ≠ layout.tagsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsOutTagSelfNe :
      layout.rhsBase + s.nodeCount + 1 ≠ layout.tagsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerYCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 2)))) by
      simp [skyReducerYCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsNodeCount)]
  rw [show (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 1)))) by
      simp [skyReducerYCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsStackSize)]
  rw [show (skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerYOutVal s)) by
      simp [skyReducerYCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsFocus)]
  rw [show (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerYStackSizeUpdatedState, skyReducerYNodeCountUpdatedState,
        skyReducerYFocusUpdatedState]]
  rw [show (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 1) (.int 0)) by
      simp [skyReducerYOutRefStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsRefsOut)]
  rw [show (skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)) by
      simp [skyReducerYOutRhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show (skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)) by
      simp [skyReducerYOutLhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show
      ((((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)).write
          (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s) =
        ((((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)).write
          (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.lhsBase + s.nodeCount + 1)
          (addr₂ := layout.rhsBase + s.nodeCount + 1)
          (v₁ := skyReducerYXVal s hstack)
          (v₂ := skyReducerYSelfVal s)
          hRhsOutLhsOutNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhsOutBefore)]
  rw [show (skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
      simp [skyReducerYOutTagStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show
      ((((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))).write
          (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s) =
        ((((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)).write
          (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app)))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.tagsBase + s.nodeCount + 1)
          (addr₂ := layout.rhsBase + s.nodeCount + 1)
          (v₁ := .int (NodeTag.code .app))
          (v₂ := skyReducerYSelfVal s)
          hRhsOutTagOutNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTagOutBefore)]
  rw [show (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount) (.int 0)) by
      simp [skyReducerYSelfRefStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)).write
          (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s) =
        ((((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)).write
          (layout.refsBase + s.nodeCount) (.int 0))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.refsBase + s.nodeCount)
          (addr₂ := layout.rhsBase + s.nodeCount + 1)
          (v₁ := .int 0)
          (v₂ := skyReducerYSelfVal s)
          hRhsOutRefNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsRefs)]
  rw [show (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)) by
      simp [skyReducerYSelfRhsStoredState, layout, skyReducerYSelfNat]]
  rw [show (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))) by
      simp [skyReducerYSelfLhsStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))).write
          (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack) =
        ((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
          (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus)))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.lhsBase + s.nodeCount)
          (addr₂ := layout.rhsBase + s.nodeCount)
          (v₁ := .int (Int.ofNat s.focus))
          (v₂ := skyReducerYXVal s hstack)
          hRhsSelfLhsSelfNe.symm)]
  rw [show
      (((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
              (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
            (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))).write
          (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s) =
        (((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
              (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
            (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)).write
          (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus)))) by
      simpa using
        (heap_write_comm
          (heap := (((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)))
          (addr₁ := layout.lhsBase + s.nodeCount)
          (addr₂ := layout.rhsBase + s.nodeCount + 1)
          (v₁ := .int (Int.ofNat s.focus))
          (v₂ := skyReducerYSelfVal s)
          hRhsOutLhsSelfNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhsSelfBefore)]
  rw [show (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
      simp [skyReducerYSelfTagStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))).write
          (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack) =
        ((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
          (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app)))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYXLoadedState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.tagsBase + s.nodeCount)
          (addr₂ := layout.rhsBase + s.nodeCount)
          (v₁ := .int (NodeTag.code .app))
          (v₂ := skyReducerYXVal s hstack)
          hRhsSelfTagSelfNe.symm)]
  rw [show
      (((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
              (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
            (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))).write
          (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s) =
        (((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
              (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
            (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)).write
          (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app)))) by
      simpa using
        (heap_write_comm
          (heap := (((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)))
          (addr₁ := layout.tagsBase + s.nodeCount)
          (addr₂ := layout.rhsBase + s.nodeCount + 1)
          (v₁ := .int (NodeTag.code .app))
          (v₂ := skyReducerYSelfVal s)
          hRhsOutTagSelfNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTagSelfBefore)]
  rw [show (skyReducerYXLoadedState s oracleVals hfocus hstack).heap =
      encodeHeapWithLayout layout s oracleVals by
      simp [skyReducerYXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
        skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
        encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap, layout]]
  have hRhsBaseRead :
      readNatArray? (encodeHeapWithLayout layout s oracleVals) layout.rhsBase s.nodeCount =
        some s.rhs := by
    simpa [layout, hrhs] using readRhs_encodeHeapWithLayout s oracleVals hrhs hnodes
  have hxVal : skyReducerYXVal s hstack = .int (Int.ofNat xNat) := by
    simp [skyReducerYXVal, xNat]
  rw [hxVal]
  simpa [layout, xNat, skyReducerYSelfVal, skyReducerYSelfNat] using
    (readNatArray?_append_two_at_end
      (heap := encodeHeapWithLayout layout s oracleVals)
      (base := layout.rhsBase)
      (count := s.nodeCount)
      (xs := s.rhs)
      (a := xNat)
      (b := s.nodeCount)
      hRhsBaseRead)

theorem readOracleRefs_skyReducerYCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes) :
    readNatArray? (skyReducerYCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).refsBase (s.nodeCount + 2) =
        some ((s.oracleRefs.push 0).push 0) := by
  rcases hwf with ⟨_hlhs, _hrhs, hrefs, hnodes, _hstackBound⟩
  let layout := layoutForState s oracleVals
  have hRefsNodeCount :
      layout.refsBase + (s.nodeCount + 2) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefsStackSize :
      layout.refsBase + (s.nodeCount + 2) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefsFocus :
      layout.refsBase + (s.nodeCount + 2) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagSelfBefore : layout.tagsBase + s.nodeCount < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagOutBefore : layout.tagsBase + s.nodeCount + 1 < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsSelfBefore : layout.lhsBase + s.nodeCount < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsOutBefore : layout.lhsBase + s.nodeCount + 1 < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsSelfBefore : layout.rhsBase + s.nodeCount < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsOutBefore : layout.rhsBase + s.nodeCount + 1 < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefOutRhsOutNe :
      layout.refsBase + s.nodeCount + 1 ≠ layout.rhsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefOutLhsOutNe :
      layout.refsBase + s.nodeCount + 1 ≠ layout.lhsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefOutTagOutNe :
      layout.refsBase + s.nodeCount + 1 ≠ layout.tagsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefSelfRhsSelfNe :
      layout.refsBase + s.nodeCount ≠ layout.rhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefOutRhsSelfNe :
      layout.refsBase + s.nodeCount + 1 ≠ layout.rhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefSelfLhsSelfNe :
      layout.refsBase + s.nodeCount ≠ layout.lhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefOutLhsSelfNe :
      layout.refsBase + s.nodeCount + 1 ≠ layout.lhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefSelfTagSelfNe :
      layout.refsBase + s.nodeCount ≠ layout.tagsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefOutTagSelfNe :
      layout.refsBase + s.nodeCount + 1 ≠ layout.tagsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerYCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 2)))) by
      simp [skyReducerYCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsNodeCount)]
  rw [show (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 1)))) by
      simp [skyReducerYCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsStackSize)]
  rw [show (skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerYOutVal s)) by
      simp [skyReducerYCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsFocus)]
  rw [show (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerYStackSizeUpdatedState, skyReducerYNodeCountUpdatedState,
        skyReducerYFocusUpdatedState]]
  rw [show (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 1) (.int 0)) by
      simp [skyReducerYOutRefStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show (skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)) by
      simp [skyReducerYOutRhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show
      ((((skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)).write
          (layout.refsBase + s.nodeCount + 1) (.int 0) =
        ((((skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount + 1) (.int 0)).write
          (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.refsBase + s.nodeCount + 1)
          (addr₂ := layout.rhsBase + s.nodeCount + 1)
          (v₁ := .int 0)
          (v₂ := skyReducerYSelfVal s)
          hRefOutRhsOutNe).symm]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hRhsOutBefore)]
  rw [show (skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)) by
      simp [skyReducerYOutLhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show
      ((((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)).write
          (layout.refsBase + s.nodeCount + 1) (.int 0) =
        ((((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount + 1) (.int 0)).write
          (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.lhsBase + s.nodeCount + 1)
          (addr₂ := layout.refsBase + s.nodeCount + 1)
          (v₁ := skyReducerYXVal s hstack)
          (v₂ := .int 0)
          hRefOutLhsOutNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhsOutBefore)]
  rw [show (skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
      simp [skyReducerYOutTagStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [show
      ((((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))).write
          (layout.refsBase + s.nodeCount + 1) (.int 0) =
        ((((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount + 1) (.int 0)).write
          (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app)))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.tagsBase + s.nodeCount + 1)
          (addr₂ := layout.refsBase + s.nodeCount + 1)
          (v₁ := .int (NodeTag.code .app))
          (v₂ := .int 0)
          hRefOutTagOutNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTagOutBefore)]
  rw [show (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount) (.int 0)) by
      simp [skyReducerYSelfRefStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)).write
          (layout.refsBase + s.nodeCount + 1) (.int 0) =
        (((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.refsBase + s.nodeCount) (.int 0)).write
          (layout.refsBase + s.nodeCount + 1) (.int 0)) by rfl]
  rw [show (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)) by
      simp [skyReducerYSelfRhsStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
          (layout.refsBase + s.nodeCount) (.int 0) =
        ((((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)).write
          (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.rhsBase + s.nodeCount)
          (addr₂ := layout.refsBase + s.nodeCount)
          (v₁ := skyReducerYXVal s hstack)
          (v₂ := .int 0)
          hRefSelfRhsSelfNe.symm)]
  rw [show
      (((((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
              (layout.refsBase + s.nodeCount) (.int 0)).write
            (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)).write
          (layout.refsBase + s.nodeCount + 1) (.int 0) =
        (((((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
              (layout.refsBase + s.nodeCount) (.int 0)).write
            (layout.refsBase + s.nodeCount + 1) (.int 0)).write
          (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack))) by
      simpa using
        (heap_write_comm
          (heap := (((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)))
          (addr₁ := layout.rhsBase + s.nodeCount)
          (addr₂ := layout.refsBase + s.nodeCount + 1)
          (v₁ := skyReducerYXVal s hstack)
          (v₂ := .int 0)
          hRefOutRhsSelfNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hRhsSelfBefore)]
  rw [show (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))) by
      simp [skyReducerYSelfLhsStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))).write
          (layout.refsBase + s.nodeCount) (.int 0) =
        ((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)).write
          (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus)))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.lhsBase + s.nodeCount)
          (addr₂ := layout.refsBase + s.nodeCount)
          (v₁ := .int (Int.ofNat s.focus))
          (v₂ := .int 0)
          hRefSelfLhsSelfNe.symm)]
  rw [show
      (((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
              (layout.refsBase + s.nodeCount) (.int 0)).write
            (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))).write
          (layout.refsBase + s.nodeCount + 1) (.int 0) =
        (((((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
              (layout.refsBase + s.nodeCount) (.int 0)).write
            (layout.refsBase + s.nodeCount + 1) (.int 0)).write
          (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus)))) by
      simpa using
        (heap_write_comm
          (heap := (((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)))
          (addr₁ := layout.lhsBase + s.nodeCount)
          (addr₂ := layout.refsBase + s.nodeCount + 1)
          (v₁ := .int (Int.ofNat s.focus))
          (v₂ := .int 0)
          hRefOutLhsSelfNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhsSelfBefore)]
  rw [show (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
      simp [skyReducerYSelfTagStoredState, layout, skyReducerYSelfNat]]
  rw [show
      ((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))).write
          (layout.refsBase + s.nodeCount) (.int 0) =
        ((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)).write
          (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app)))) by
      simpa using
        (heap_write_comm
          (heap := (skyReducerYXLoadedState s oracleVals hfocus hstack).heap)
          (addr₁ := layout.tagsBase + s.nodeCount)
          (addr₂ := layout.refsBase + s.nodeCount)
          (v₁ := .int (NodeTag.code .app))
          (v₂ := .int 0)
          hRefSelfTagSelfNe.symm)]
  rw [show
      (((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
              (layout.refsBase + s.nodeCount) (.int 0)).write
            (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))).write
          (layout.refsBase + s.nodeCount + 1) (.int 0) =
        (((((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
              (layout.refsBase + s.nodeCount) (.int 0)).write
            (layout.refsBase + s.nodeCount + 1) (.int 0)).write
          (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app)))) by
      simpa using
        (heap_write_comm
          (heap := (((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
            (layout.refsBase + s.nodeCount) (.int 0)))
          (addr₁ := layout.tagsBase + s.nodeCount)
          (addr₂ := layout.refsBase + s.nodeCount + 1)
          (v₁ := .int (NodeTag.code .app))
          (v₂ := .int 0)
          hRefOutTagSelfNe.symm)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTagSelfBefore)]
  rw [show (skyReducerYXLoadedState s oracleVals hfocus hstack).heap =
      encodeHeapWithLayout layout s oracleVals by
      simp [skyReducerYXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
        skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
        encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap, layout]]
  have hRefsBaseRead :
      readNatArray? (encodeHeapWithLayout layout s oracleVals) layout.refsBase s.nodeCount =
        some s.oracleRefs := by
    simpa [layout, hrefs] using readOracleRefs_encodeHeapWithLayout s oracleVals hrefs hnodes
  simpa [layout] using
    (readNatArray?_append_two_at_end
      (heap := encodeHeapWithLayout layout s oracleVals)
      (base := layout.refsBase)
      (count := s.nodeCount)
      (xs := s.oracleRefs)
      (a := 0)
      (b := 0)
      hRefsBaseRead)

theorem readStack_skyReducerYCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) (hcap : s.nodeCount + 2 ≤ s.maxNodes) :
    readNatArray? (skyReducerYCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).stackBase (s.stack.length - 1) =
        some ((s.stack.drop 1).reverse.toArray) := by
  let layout := layoutForState s oracleVals
  have hStackNodeCount :
      layout.stackBase + (s.stack.length - 1) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackStackSize :
      layout.stackBase + (s.stack.length - 1) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackFocus :
      layout.stackBase + (s.stack.length - 1) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRefs :
      layout.refsBase + s.nodeCount + 1 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRhsOut :
      layout.rhsBase + s.nodeCount + 1 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackLhsOut :
      layout.lhsBase + s.nodeCount + 1 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackTagOut :
      layout.tagsBase + s.nodeCount + 1 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRefsSelf :
      layout.refsBase + s.nodeCount < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRhsSelf :
      layout.rhsBase + s.nodeCount < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackLhsSelf :
      layout.lhsBase + s.nodeCount < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackTagSelf :
      layout.tagsBase + s.nodeCount < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerYCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 2)))) by
      simp [skyReducerYCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [show (skyReducerYCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 1)))) by
      simp [skyReducerYCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [show (skyReducerYCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerYOutVal s)) by
      simp [skyReducerYCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  rw [show (skyReducerYStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerYStackSizeUpdatedState, skyReducerYNodeCountUpdatedState,
        skyReducerYFocusUpdatedState]]
  rw [show (skyReducerYOutRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 1) (.int 0)) by
      simp [skyReducerYOutRefStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRefs)]
  rw [show (skyReducerYOutRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 1) (skyReducerYSelfVal s)) by
      simp [skyReducerYOutRhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRhsOut)]
  rw [show (skyReducerYOutLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount + 1) (skyReducerYXVal s hstack)) by
      simp [skyReducerYOutLhsStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackLhsOut)]
  rw [show (skyReducerYOutTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
      simp [skyReducerYOutTagStoredState, layout, skyReducerYOutNat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackTagOut)]
  rw [show (skyReducerYSelfRefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount) (.int 0)) by
      simp [skyReducerYSelfRefStoredState, layout, skyReducerYSelfNat]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRefsSelf)]
  rw [show (skyReducerYSelfRhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount) (skyReducerYXVal s hstack)) by
      simp [skyReducerYSelfRhsStoredState, layout, skyReducerYSelfNat]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRhsSelf)]
  rw [show (skyReducerYSelfLhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount) (.int (Int.ofNat s.focus))) by
      simp [skyReducerYSelfLhsStoredState, layout, skyReducerYSelfNat]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackLhsSelf)]
  rw [show (skyReducerYSelfTagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerYXLoadedState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
      simp [skyReducerYSelfTagStoredState, layout, skyReducerYSelfNat]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackTagSelf)]
  rw [show (skyReducerYXLoadedState s oracleVals hfocus hstack).heap =
      encodeHeapWithLayout layout s oracleVals by
      simp [skyReducerYXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
        skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
        encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap, layout]]
  cases hs : s.stack with
  | nil =>
      have : False := by
        simpa [hs] using hstack
      contradiction
  | cons x rest =>
      have hRev : (x :: rest).reverse = rest.reverse ++ [x] := by
        simp
      have hStackNodeCount' :
          layout.stackBase + ((x :: rest).length - 1) ≤ layout.nodeCountBase := by
        simpa [hs] using hStackNodeCount
      have hStackStackSize' :
          layout.stackBase + ((x :: rest).length - 1) ≤ layout.stackSizeBase := by
        simpa [hs] using hStackStackSize
      have hStackFocus' :
          layout.stackBase + ((x :: rest).length - 1) ≤ layout.focusBase := by
        simpa [hs] using hStackFocus
      rw [show encodeHeapWithLayout layout s oracleVals =
          ((((encodeStackWithLayout layout s oracleVals).write layout.focusBase (.int (Int.ofNat s.focus))).write
            layout.stackSizeBase (.int (Int.ofNat s.stack.length))).write
            layout.nodeCountBase (.int (Int.ofNat s.nodeCount))) by
          simp [encodeHeapWithLayout, layout]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount')]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize')]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus')]
      rw [show encodeStackWithLayout layout s oracleVals =
          writeNatList (encodeOracleValuesWithLayout layout s oracleVals)
            layout.stackBase ((x :: rest).reverse) by
          simp [encodeStackWithLayout, hs]]
      rw [hRev, writeNatList_append]
      have hSuffix :
          layout.stackBase + rest.length ≤ layout.stackBase + rest.reverse.length := by
        simp
      have hRead :
          readNatArray?
            (writeNatList
              (writeNatList (encodeOracleValuesWithLayout layout s oracleVals) layout.stackBase
                rest.reverse)
              (layout.stackBase + rest.reverse.length) [x])
            layout.stackBase rest.length =
              some (rest.reverse.toArray) := by
        rw [readNatArray?_writeNatList_otherRange _ _ _ layout.stackBase rest.length hSuffix]
        simpa [layout, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (readNatArray?_writeNatList
            (heap := encodeOracleValuesWithLayout layout s oracleVals)
            (base := layout.stackBase) (xs := rest.reverse))
      simpa [hs] using hRead

theorem readFocus_skyReducerKCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    readNatCell? (skyReducerKCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).focusBase =
        some (s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩) := by
  have hFocusNeNodeCountBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hFocusNeStackSizeBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerKCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerKCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeNodeCountBase]
  rw [show (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerKCommittedStackSizeState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeStackSizeBase]
  simpa [skyReducerKCommittedFocusState, skyReducerKXVal]
    using (readNatCell?_write_same
      (heap := (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).heap)
      (addr := (layoutForState s oracleVals).focusBase)
      (n := s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩))

theorem readStackSize_skyReducerKCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    readNatCell? (skyReducerKCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).stackSizeBase = some (s.stack.length - 2) := by
  have hStackSizeNeNodeCountBase :
      (layoutForState s oracleVals).stackSizeBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerKCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerKCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hStackSizeNeNodeCountBase]
  simpa [skyReducerKCommittedStackSizeState]
    using (readNatCell?_write_same
      (heap := (skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap)
      (addr := (layoutForState s oracleVals).stackSizeBase)
      (n := s.stack.length - 2))

theorem readNodeCount_skyReducerKCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    readNatCell? (skyReducerKCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).nodeCountBase = some s.nodeCount := by
  simpa [skyReducerKCommittedState]
    using (readNatCell?_write_same
      (heap := (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap)
      (addr := (layoutForState s oracleVals).nodeCountBase)
      (n := s.nodeCount))

theorem readTags_skyReducerKCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readIntArray? (skyReducerKCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).tagsBase s.nodeCount = some s.tags := by
  rcases hwf with ⟨_hlhs, _hrhs, _hrefs, hnodes, _hstack⟩
  have hTagsNodeCount :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsStackSize :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsFocus :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerKCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerKCommittedState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsNodeCount)]
  rw [show (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerKCommittedStackSizeState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsStackSize)]
  rw [show (skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).focusBase (skyReducerKXVal s hstack)) by
      simp [skyReducerKCommittedFocusState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsFocus)]
  simpa [skyReducerKStackSizeUpdatedState, skyReducerKFocusUpdatedState, skyReducerKXLoadedState,
    skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout]
    using readTags_encodeHeapWithLayout s oracleVals hnodes

theorem readLhs_skyReducerKCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatArray? (skyReducerKCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).lhsBase s.nodeCount = some s.lhs := by
  rcases hwf with ⟨hlhs, _hrhs, _hrefs, hnodes, _hstack⟩
  have hLhsNodeCount :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsStackSize :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsFocus :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerKCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerKCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsNodeCount)]
  rw [show (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerKCommittedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsStackSize)]
  rw [show (skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).focusBase (skyReducerKXVal s hstack)) by
      simp [skyReducerKCommittedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsFocus)]
  simpa [skyReducerKStackSizeUpdatedState, skyReducerKFocusUpdatedState, skyReducerKXLoadedState,
    skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, hlhs]
    using readLhs_encodeHeapWithLayout s oracleVals hlhs hnodes

theorem readRhs_skyReducerKCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatArray? (skyReducerKCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).rhsBase s.nodeCount = some s.rhs := by
  rcases hwf with ⟨_hlhs, hrhs, _hrefs, hnodes, _hstack⟩
  have hRhsNodeCount :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsStackSize :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsFocus :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerKCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerKCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsNodeCount)]
  rw [show (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerKCommittedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsStackSize)]
  rw [show (skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).focusBase (skyReducerKXVal s hstack)) by
      simp [skyReducerKCommittedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsFocus)]
  simpa [skyReducerKStackSizeUpdatedState, skyReducerKFocusUpdatedState, skyReducerKXLoadedState,
    skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, hrhs]
    using readRhs_encodeHeapWithLayout s oracleVals hrhs hnodes

theorem readOracleRefs_skyReducerKCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatArray? (skyReducerKCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).refsBase s.nodeCount = some s.oracleRefs := by
  rcases hwf with ⟨_hlhs, _hrhs, hrefs, hnodes, _hstack⟩
  have hRefsNodeCount :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsStackSize :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsFocus :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerKCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerKCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsNodeCount)]
  rw [show (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerKCommittedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsStackSize)]
  rw [show (skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).focusBase (skyReducerKXVal s hstack)) by
      simp [skyReducerKCommittedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsFocus)]
  simpa [skyReducerKStackSizeUpdatedState, skyReducerKFocusUpdatedState, skyReducerKXLoadedState,
    skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, hrefs]
    using readOracleRefs_encodeHeapWithLayout s oracleVals hrefs hnodes

theorem readStack_skyReducerKCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 2 ≤ s.stack.length) :
    readNatArray? (skyReducerKCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).stackBase (s.stack.length - 2) =
        some ((s.stack.drop 2).reverse.toArray) := by
  let layout := layoutForState s oracleVals
  have hStackNodeCount :
      layout.stackBase + (s.stack.length - 2) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackStackSize :
      layout.stackBase + (s.stack.length - 2) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackFocus :
      layout.stackBase + (s.stack.length - 2) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerKCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerKCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [show (skyReducerKCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerKCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [show (skyReducerKCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerKXVal s hstack)) by
      simp [skyReducerKCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  rw [show (skyReducerKStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      encodeHeapWithLayout layout s oracleVals by
      simp [skyReducerKStackSizeUpdatedState, skyReducerKFocusUpdatedState, skyReducerKXLoadedState,
        skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
        skyReducerFocusLoadedState, skyReducerEntry, layout, encodeExecStateWithLayout]]
  rw [show encodeHeapWithLayout layout s oracleVals =
      ((((encodeStackWithLayout layout s oracleVals).write layout.focusBase (.int (Int.ofNat s.focus))).write
        layout.stackSizeBase (.int (Int.ofNat s.stack.length))).write
        layout.nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [encodeHeapWithLayout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  cases hs : s.stack with
  | nil =>
      have : False := by
        simpa [hs] using hstack
      contradiction
  | cons x xs =>
      cases xs with
      | nil =>
          have : False := by
            simpa [hs] using hstack
          contradiction
      | cons y rest =>
          have hRev : (x :: y :: rest).reverse = rest.reverse ++ [y, x] := by
            simp
          rw [show encodeStackWithLayout layout s oracleVals =
              writeNatList (encodeOracleValuesWithLayout layout s oracleVals)
                layout.stackBase ((x :: y :: rest).reverse) by
              simp [encodeStackWithLayout, hs]]
          rw [hRev, writeNatList_append]
          have hSuffix :
              layout.stackBase + rest.length ≤ layout.stackBase + rest.reverse.length := by
            simp
          have hRead :
              readNatArray?
                (writeNatList
                  (writeNatList (encodeOracleValuesWithLayout layout s oracleVals) layout.stackBase
                    rest.reverse)
                  (layout.stackBase + rest.reverse.length) [y, x])
                layout.stackBase rest.length =
                  some (rest.reverse.toArray) := by
            rw [readNatArray?_writeNatList_otherRange _ _ _ layout.stackBase rest.length hSuffix]
            simpa [layout, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (readNatArray?_writeNatList
                (heap := encodeOracleValuesWithLayout layout s oracleVals)
                (base := layout.stackBase) (xs := rest.reverse))
          simpa using hRead

theorem decodeKernelState?_skyReducerYCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (skyReducerYCommittedState s oracleVals hfocus hstack) =
        some (skyReducerYNextState s hstack) := by
  rw [decodeKernelState?]
  rw [readFocus_skyReducerYCommittedState]
  rw [readStackSize_skyReducerYCommittedState]
  rw [readNodeCount_skyReducerYCommittedState]
  simp [skyReducerYNextState, skyReducerYOutNat]
  rw [readTags_skyReducerYCommittedState s oracleVals hwf hfocus hstack hcap]
  rw [readLhs_skyReducerYCommittedState s oracleVals hwf hfocus hstack hcap]
  rw [readRhs_skyReducerYCommittedState s oracleVals hwf hfocus hstack hcap]
  rw [readOracleRefs_skyReducerYCommittedState s oracleVals hwf hfocus hstack hcap]
  rw [readStack_skyReducerYCommittedState s oracleVals hfocus hstack hcap]
  simp [skyReducerYNextState, skyReducerYOutNat]

theorem runLoweredStep?_y
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.nodeCount + 2 ≤ s.maxNodes)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    runLoweredStep? s oracleVals =
      some (.progress, skyReducerYNextState s hstack) := by
  simp [runLoweredStep?]
  rw [execStmt_yPath_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack hcap hy]
  simp [StepStatus.ofCode?, StepStatus.code]
  rw [decodeKernelState?_skyReducerYCommittedState s oracleVals hwf hfocus hstack hcap]
  simp [StepStatus.ofCode?, StepStatus.code]

theorem readFocus_skyReducerSCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    readNatCell? (skyReducerSCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).focusBase = some (s.nodeCount + 2) := by
  have hFocusNeNodeCountBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hFocusNeStackSizeBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerSCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat (s.nodeCount + 3)))) by
      simp [skyReducerSCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeNodeCountBase]
  rw [show (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 3)))) by
      simp [skyReducerSCommittedStackSizeState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeStackSizeBase]
  simpa [skyReducerSCommittedFocusState, skyReducerSNode2Val, skyReducerSNode2Nat]
    using (readNatCell?_write_same
      (heap := (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap)
      (addr := (layoutForState s oracleVals).focusBase)
      (n := s.nodeCount + 2))

theorem readStackSize_skyReducerSCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    readNatCell? (skyReducerSCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).stackSizeBase = some (s.stack.length - 3) := by
  have hStackSizeNeNodeCountBase :
      (layoutForState s oracleVals).stackSizeBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerSCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat (s.nodeCount + 3)))) by
      simp [skyReducerSCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hStackSizeNeNodeCountBase]
  simpa [skyReducerSCommittedStackSizeState]
    using (readNatCell?_write_same
      (heap := (skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap)
      (addr := (layoutForState s oracleVals).stackSizeBase)
      (n := s.stack.length - 3))

theorem readNodeCount_skyReducerSCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    readNatCell? (skyReducerSCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).nodeCountBase = some (s.nodeCount + 3) := by
  simpa [skyReducerSCommittedState]
    using (readNatCell?_write_same
      (heap := (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap)
      (addr := (layoutForState s oracleVals).nodeCountBase)
      (n := s.nodeCount + 3))
theorem readTags_skyReducerSCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes) :
    readIntArray? (skyReducerSCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).tagsBase (s.nodeCount + 3) =
        some (((s.tags.push (NodeTag.code .app)).push (NodeTag.code .app)).push
          (NodeTag.code .app)) := by
  let layout := layoutForState s oracleVals
  have hTagsNodeCount :
      layout.tagsBase + (s.nodeCount + 3) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsStackSize :
      layout.tagsBase + (s.nodeCount + 3) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsFocus :
      layout.tagsBase + (s.nodeCount + 3) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerSCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 3)))) by
      simp [skyReducerSCommittedState, layout]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsNodeCount)]
  rw [show (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 3)))) by
      simp [skyReducerSCommittedStackSizeState, layout]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsStackSize)]
  rw [show (skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerSNode2Val s)) by
      simp [skyReducerSCommittedFocusState, layout]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsFocus)]
  rw [show (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerSStackSizeUpdatedState, skyReducerSNodeCountUpdatedState,
        skyReducerSFocusUpdatedState]]
  have hTagsBaseRead :
      readIntArray? (encodeHeapWithLayout layout s oracleVals) layout.tagsBase s.nodeCount =
        some s.tags := by
    simpa [layout] using readTags_encodeHeapWithLayout s oracleVals (by omega)
  have hTagsLhs0 :
      layout.tagsBase + (s.nodeCount + 1) ≤ layout.lhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRhs0 :
      layout.tagsBase + (s.nodeCount + 1) ≤ layout.rhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRefs0 :
      layout.tagsBase + (s.nodeCount + 1) ≤ layout.refsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsLhs1 :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.lhsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRhs1 :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.rhsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRefs1 :
      layout.tagsBase + (s.nodeCount + 2) ≤ layout.refsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsLhs2 :
      layout.tagsBase + (s.nodeCount + 3) ≤ layout.lhsBase + s.nodeCount + 2 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRhs2 :
      layout.tagsBase + (s.nodeCount + 3) ≤ layout.rhsBase + s.nodeCount + 2 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsRefs2 :
      layout.tagsBase + (s.nodeCount + 3) ≤ layout.refsBase + s.nodeCount + 2 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTagsNode0 :
      readIntArray? (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap
        layout.tagsBase (s.nodeCount + 1) =
          some (s.tags.push (NodeTag.code .app)) := by
    rw [show (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.refsBase + s.nodeCount) (.int 0)) by
        simp [skyReducerSNode0RefStoredState, layout, skyReducerSNode0Nat]]
    rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRefs0)]
    rw [show (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.rhsBase + s.nodeCount) (skyReducerSZVal s hstack)) by
        simp [skyReducerSNode0RhsStoredState, layout, skyReducerSNode0Nat]]
    rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRhs0)]
    rw [show (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap).write
          (layout.lhsBase + s.nodeCount) (skyReducerSXVal s hstack)) by
        simp [skyReducerSNode0LhsStoredState, layout, skyReducerSNode0Nat]]
    rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsLhs0)]
    rw [show (skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap =
        ((encodeHeapWithLayout layout s oracleVals).write
          (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
        simp [skyReducerSNode0TagStoredState, skyReducerSXYZLoadedState, skyReducerSXYLoadedState,
          skyReducerSXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
          skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
          encodeExecStateWithLayout, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
          skyReducerSNode0Nat, layout]]
    simpa [layout] using
      (readIntArray?_append_one_at_end
        (heap := encodeHeapWithLayout layout s oracleVals)
        (base := layout.tagsBase)
        (count := s.nodeCount)
        (xs := s.tags)
        (a := NodeTag.code .app)
        hTagsBaseRead)
  have hTagsNode1 :
      readIntArray? (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap
        layout.tagsBase (s.nodeCount + 2) =
          some ((s.tags.push (NodeTag.code .app)).push (NodeTag.code .app)) := by
    rw [show (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.refsBase + s.nodeCount + 1) (.int 0)) by
        simp [skyReducerSNode1RefStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRefs1)]
    rw [show (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.rhsBase + s.nodeCount + 1) (skyReducerSZVal s hstack)) by
        simp [skyReducerSNode1RhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRhs1)]
    rw [show (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap).write
          (layout.lhsBase + s.nodeCount + 1) (skyReducerSYVal s hstack)) by
        simp [skyReducerSNode1LhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsLhs1)]
    rw [show (skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap).write
          (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
        simp [skyReducerSNode1TagStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    simpa [layout] using
      (readIntArray?_append_one_at_end
        (heap := (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap)
        (base := layout.tagsBase)
        (count := s.nodeCount + 1)
        (xs := s.tags.push (NodeTag.code .app))
        (a := NodeTag.code .app)
        hTagsNode0)
  rw [show (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 2) (.int 0)) by
      simp [skyReducerSNode2RefStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRefs2)]
  rw [show (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 2) (skyReducerSNode1Val s)) by
      simp [skyReducerSNode2RhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsRhs2)]
  rw [show (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount + 2) (skyReducerSNode0Val s)) by
      simp [skyReducerSNode2LhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsLhs2)]
  rw [show (skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 2) (.int (NodeTag.code .app))) by
      simp [skyReducerSNode2TagStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  simpa [layout] using
    (readIntArray?_append_one_at_end
      (heap := (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap)
      (base := layout.tagsBase)
      (count := s.nodeCount + 2)
      (xs := (s.tags.push (NodeTag.code .app)).push (NodeTag.code .app))
      (a := NodeTag.code .app)
      hTagsNode1)

theorem readLhs_skyReducerSCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes) :
    readNatArray? (skyReducerSCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).lhsBase (s.nodeCount + 3) =
        some (((s.lhs.push (s.stack.get ⟨0, by omega⟩)).push
          (s.stack.get ⟨1, by omega⟩)).push s.nodeCount) := by
  rcases hwf with ⟨hlhs, _hrhs, _hrefs, hnodes, _hstackBound⟩
  let layout := layoutForState s oracleVals
  let xNat := s.stack.get ⟨0, by omega⟩
  let yNat := s.stack.get ⟨1, by omega⟩
  have hLhsNodeCount :
      layout.lhsBase + (s.nodeCount + 3) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsStackSize :
      layout.lhsBase + (s.nodeCount + 3) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsFocus :
      layout.lhsBase + (s.nodeCount + 3) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRhs0 :
      layout.lhsBase + (s.nodeCount + 1) ≤ layout.rhsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRefs0 :
      layout.lhsBase + (s.nodeCount + 1) ≤ layout.refsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRhs1 :
      layout.lhsBase + (s.nodeCount + 2) ≤ layout.rhsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRefs1 :
      layout.lhsBase + (s.nodeCount + 2) ≤ layout.refsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRhs2 :
      layout.lhsBase + (s.nodeCount + 3) ≤ layout.rhsBase + s.nodeCount + 2 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhsRefs2 :
      layout.lhsBase + (s.nodeCount + 3) ≤ layout.refsBase + s.nodeCount + 2 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTag0Before : layout.tagsBase + s.nodeCount < layout.lhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTag1Before : layout.tagsBase + s.nodeCount + 1 < layout.lhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTag2Before : layout.tagsBase + s.nodeCount + 2 < layout.lhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerSCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 3)))) by
      simp [skyReducerSCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsNodeCount)]
  rw [show (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 3)))) by
      simp [skyReducerSCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsStackSize)]
  rw [show (skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerSNode2Val s)) by
      simp [skyReducerSCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsFocus)]
  rw [show (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerSStackSizeUpdatedState, skyReducerSNodeCountUpdatedState,
        skyReducerSFocusUpdatedState]]
  have hLhsBaseRead :
      readNatArray? (encodeHeapWithLayout layout s oracleVals) layout.lhsBase s.nodeCount =
        some s.lhs := by
    simpa [layout, hlhs] using readLhs_encodeHeapWithLayout s oracleVals hlhs hnodes
  have hxVal : skyReducerSXVal s hstack = .int (Int.ofNat xNat) := by
    simp [skyReducerSXVal, xNat]
  have hyVal : skyReducerSYVal s hstack = .int (Int.ofNat yNat) := by
    simp [skyReducerSYVal, yNat]
  have hNode0Val : skyReducerSNode0Val s = .int (Int.ofNat s.nodeCount) := by
    simp [skyReducerSNode0Val, skyReducerSNode0Nat]
  have hLhsNode0 :
      readNatArray? (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap
        layout.lhsBase (s.nodeCount + 1) =
          some (s.lhs.push xNat) := by
    rw [show (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.refsBase + s.nodeCount) (.int 0)) by
        simp [skyReducerSNode0RefStoredState, layout, skyReducerSNode0Nat]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRefs0)]
    rw [show (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.rhsBase + s.nodeCount) (skyReducerSZVal s hstack)) by
        simp [skyReducerSNode0RhsStoredState, layout, skyReducerSNode0Nat]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRhs0)]
    rw [show (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap).write
          (layout.lhsBase + s.nodeCount) (skyReducerSXVal s hstack)) by
        simp [skyReducerSNode0LhsStoredState, layout, skyReducerSNode0Nat]]
    rw [show (skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap =
        ((encodeHeapWithLayout layout s oracleVals).write
          (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
        simp [skyReducerSNode0TagStoredState, skyReducerSXYZLoadedState, skyReducerSXYLoadedState,
          skyReducerSXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
          skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
          encodeExecStateWithLayout, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
          skyReducerSNode0Nat, layout]]
    have hLhsAfterTag0 :
        readNatArray?
            ((encodeHeapWithLayout layout s oracleVals).write
              (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app)))
            layout.lhsBase s.nodeCount =
          some s.lhs := by
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTag0Before)]
      exact hLhsBaseRead
    rw [hxVal]
    simpa [layout, xNat] using
      (readNatArray?_append_one_at_end
        (heap := ((encodeHeapWithLayout layout s oracleVals).write
          (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))))
        (base := layout.lhsBase)
        (count := s.nodeCount)
        (xs := s.lhs)
        (a := xNat)
        hLhsAfterTag0)
  have hLhsNode1 :
      readNatArray? (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap
        layout.lhsBase (s.nodeCount + 2) =
          some ((s.lhs.push xNat).push yNat) := by
    rw [show (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.refsBase + s.nodeCount + 1) (.int 0)) by
        simp [skyReducerSNode1RefStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRefs1)]
    rw [show (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.rhsBase + s.nodeCount + 1) (skyReducerSZVal s hstack)) by
        simp [skyReducerSNode1RhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRhs1)]
    rw [show (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap).write
          (layout.lhsBase + s.nodeCount + 1) (skyReducerSYVal s hstack)) by
        simp [skyReducerSNode1LhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    rw [show (skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap).write
          (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
        simp [skyReducerSNode1TagStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    have hLhsAfterTag1 :
        readNatArray?
            (((skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap).write
              (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app)))
            layout.lhsBase (s.nodeCount + 1) =
          some (s.lhs.push xNat) := by
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTag1Before)]
      exact hLhsNode0
    rw [hyVal]
    simpa [layout, yNat] using
      (readNatArray?_append_one_at_end
        (heap := (((skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap).write
          (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))))
        (base := layout.lhsBase)
        (count := s.nodeCount + 1)
        (xs := s.lhs.push xNat)
        (a := yNat)
        hLhsAfterTag1)
  rw [show (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 2) (.int 0)) by
      simp [skyReducerSNode2RefStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRefs2)]
  rw [show (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 2) (skyReducerSNode1Val s)) by
      simp [skyReducerSNode2RhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsRhs2)]
  rw [show (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount + 2) (skyReducerSNode0Val s)) by
      simp [skyReducerSNode2LhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [show (skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 2) (.int (NodeTag.code .app))) by
      simp [skyReducerSNode2TagStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  have hLhsAfterTag2 :
      readNatArray?
          (((skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount + 2) (.int (NodeTag.code .app)))
          layout.lhsBase (s.nodeCount + 2) =
        some ((s.lhs.push xNat).push yNat) := by
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTag2Before)]
    exact hLhsNode1
  rw [hNode0Val]
  simpa [layout, xNat, yNat] using
    (readNatArray?_append_one_at_end
      (heap := (((skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 2) (.int (NodeTag.code .app))))
      (base := layout.lhsBase)
      (count := s.nodeCount + 2)
      (xs := (s.lhs.push xNat).push yNat)
      (a := s.nodeCount)
      hLhsAfterTag2)

theorem readRhs_skyReducerSCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes) :
    readNatArray? (skyReducerSCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).rhsBase (s.nodeCount + 3) =
        some (((s.rhs.push (s.stack.get ⟨2, by omega⟩)).push
          (s.stack.get ⟨2, by omega⟩)).push (s.nodeCount + 1)) := by
  rcases hwf with ⟨_hlhs, hrhs, _hrefs, hnodes, _hstackBound⟩
  let layout := layoutForState s oracleVals
  let zNat := s.stack.get ⟨2, by omega⟩
  have hRhsNodeCount :
      layout.rhsBase + (s.nodeCount + 3) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsStackSize :
      layout.rhsBase + (s.nodeCount + 3) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhsFocus :
      layout.rhsBase + (s.nodeCount + 3) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefs0 :
      layout.rhsBase + (s.nodeCount + 1) ≤ layout.refsBase + s.nodeCount := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefs1 :
      layout.rhsBase + (s.nodeCount + 2) ≤ layout.refsBase + s.nodeCount + 1 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefs2 :
      layout.rhsBase + (s.nodeCount + 3) ≤ layout.refsBase + s.nodeCount + 2 := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTag0Before : layout.tagsBase + s.nodeCount < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTag1Before : layout.tagsBase + s.nodeCount + 1 < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTag2Before : layout.tagsBase + s.nodeCount + 2 < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhs0Before : layout.lhsBase + s.nodeCount < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhs1Before : layout.lhsBase + s.nodeCount + 1 < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhs2Before : layout.lhsBase + s.nodeCount + 2 < layout.rhsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerSCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 3)))) by
      simp [skyReducerSCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsNodeCount)]
  rw [show (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 3)))) by
      simp [skyReducerSCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsStackSize)]
  rw [show (skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerSNode2Val s)) by
      simp [skyReducerSCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsFocus)]
  rw [show (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerSStackSizeUpdatedState, skyReducerSNodeCountUpdatedState,
        skyReducerSFocusUpdatedState]]
  have hRhsBaseRead :
      readNatArray? (encodeHeapWithLayout layout s oracleVals) layout.rhsBase s.nodeCount =
        some s.rhs := by
    simpa [layout, hrhs] using readRhs_encodeHeapWithLayout s oracleVals hrhs hnodes
  have hZVal : skyReducerSZVal s hstack = .int (Int.ofNat zNat) := by
    simp [skyReducerSZVal, zNat]
  have hNode1Val : skyReducerSNode1Val s = .int (Int.ofNat (s.nodeCount + 1)) := by
    simp [skyReducerSNode1Val, skyReducerSNode1Nat]
  have hRhsNode0 :
      readNatArray? (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap
        layout.rhsBase (s.nodeCount + 1) =
          some (s.rhs.push zNat) := by
    rw [show (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.refsBase + s.nodeCount) (.int 0)) by
        simp [skyReducerSNode0RefStoredState, layout, skyReducerSNode0Nat]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefs0)]
    rw [show (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.rhsBase + s.nodeCount) (skyReducerSZVal s hstack)) by
        simp [skyReducerSNode0RhsStoredState, layout, skyReducerSNode0Nat]]
    have hRhsBeforeNode0 :
        readNatArray? (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap
          layout.rhsBase s.nodeCount =
            some s.rhs := by
      rw [show (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap =
          (((skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount) (skyReducerSXVal s hstack)) by
          simp [skyReducerSNode0LhsStoredState, layout, skyReducerSNode0Nat]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhs0Before)]
      rw [show (skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap =
          ((encodeHeapWithLayout layout s oracleVals).write
            (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
          simp [skyReducerSNode0TagStoredState, skyReducerSXYZLoadedState, skyReducerSXYLoadedState,
            skyReducerSXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
            skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
            encodeExecStateWithLayout, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
            skyReducerSNode0Nat, layout]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTag0Before)]
      exact hRhsBaseRead
    rw [hZVal]
    simpa [layout, zNat] using
      (readNatArray?_append_one_at_end
        (heap := (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap)
        (base := layout.rhsBase)
        (count := s.nodeCount)
        (xs := s.rhs)
        (a := zNat)
        hRhsBeforeNode0)
  have hRhsNode1 :
      readNatArray? (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap
        layout.rhsBase (s.nodeCount + 2) =
          some ((s.rhs.push zNat).push zNat) := by
    rw [show (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.refsBase + s.nodeCount + 1) (.int 0)) by
        simp [skyReducerSNode1RefStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefs1)]
    rw [show (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.rhsBase + s.nodeCount + 1) (skyReducerSZVal s hstack)) by
        simp [skyReducerSNode1RhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    have hRhsBeforeNode1 :
        readNatArray? (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap
          layout.rhsBase (s.nodeCount + 1) =
            some (s.rhs.push zNat) := by
      rw [show (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap =
          (((skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount + 1) (skyReducerSYVal s hstack)) by
          simp [skyReducerSNode1LhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhs1Before)]
      rw [show (skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap =
          (((skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
          simp [skyReducerSNode1TagStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTag1Before)]
      exact hRhsNode0
    rw [hZVal]
    simpa [layout, zNat] using
      (readNatArray?_append_one_at_end
        (heap := (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap)
        (base := layout.rhsBase)
        (count := s.nodeCount + 1)
        (xs := s.rhs.push zNat)
        (a := zNat)
        hRhsBeforeNode1)
  rw [show (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 2) (.int 0)) by
      simp [skyReducerSNode2RefStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefs2)]
  rw [show (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 2) (skyReducerSNode1Val s)) by
      simp [skyReducerSNode2RhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  have hRhsBeforeNode2 :
      readNatArray? (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap
        layout.rhsBase (s.nodeCount + 2) =
          some ((s.rhs.push zNat).push zNat) := by
    rw [show (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap).write
          (layout.lhsBase + s.nodeCount + 2) (skyReducerSNode0Val s)) by
        simp [skyReducerSNode2LhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhs2Before)]
    rw [show (skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap).write
          (layout.tagsBase + s.nodeCount + 2) (.int (NodeTag.code .app))) by
        simp [skyReducerSNode2TagStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTag2Before)]
    exact hRhsNode1
  rw [hNode1Val]
  simpa [layout, zNat] using
    (readNatArray?_append_one_at_end
      (heap := (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap)
      (base := layout.rhsBase)
      (count := s.nodeCount + 2)
      (xs := (s.rhs.push zNat).push zNat)
      (a := s.nodeCount + 1)
      hRhsBeforeNode2)

theorem readOracleRefs_skyReducerSCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes) :
    readNatArray? (skyReducerSCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).refsBase (s.nodeCount + 3) =
        some (((s.oracleRefs.push 0).push 0).push 0) := by
  rcases hwf with ⟨_hlhs, _hrhs, hrefs, hnodes, _hstackBound⟩
  let layout := layoutForState s oracleVals
  have hRefsNodeCount :
      layout.refsBase + (s.nodeCount + 3) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefsStackSize :
      layout.refsBase + (s.nodeCount + 3) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRefsFocus :
      layout.refsBase + (s.nodeCount + 3) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTag0Before : layout.tagsBase + s.nodeCount < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTag1Before : layout.tagsBase + s.nodeCount + 1 < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hTag2Before : layout.tagsBase + s.nodeCount + 2 < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhs0Before : layout.lhsBase + s.nodeCount < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhs1Before : layout.lhsBase + s.nodeCount + 1 < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hLhs2Before : layout.lhsBase + s.nodeCount + 2 < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhs0Before : layout.rhsBase + s.nodeCount < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhs1Before : layout.rhsBase + s.nodeCount + 1 < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hRhs2Before : layout.rhsBase + s.nodeCount + 2 < layout.refsBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerSCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 3)))) by
      simp [skyReducerSCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsNodeCount)]
  rw [show (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 3)))) by
      simp [skyReducerSCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsStackSize)]
  rw [show (skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerSNode2Val s)) by
      simp [skyReducerSCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsFocus)]
  rw [show (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerSStackSizeUpdatedState, skyReducerSNodeCountUpdatedState,
        skyReducerSFocusUpdatedState]]
  have hRefsBaseRead :
      readNatArray? (encodeHeapWithLayout layout s oracleVals) layout.refsBase s.nodeCount =
        some s.oracleRefs := by
    simpa [layout, hrefs] using readOracleRefs_encodeHeapWithLayout s oracleVals hrefs hnodes
  have hRefsNode0 :
      readNatArray? (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap
        layout.refsBase (s.nodeCount + 1) =
          some (s.oracleRefs.push 0) := by
    rw [show (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.refsBase + s.nodeCount) (.int 0)) by
        simp [skyReducerSNode0RefStoredState, layout, skyReducerSNode0Nat]]
    have hRefsBeforeNode0 :
        readNatArray? (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap
          layout.refsBase s.nodeCount =
            some s.oracleRefs := by
      rw [show (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap =
          (((skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount) (skyReducerSZVal s hstack)) by
          simp [skyReducerSNode0RhsStoredState, layout, skyReducerSNode0Nat]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hRhs0Before)]
      rw [show (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap =
          (((skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount) (skyReducerSXVal s hstack)) by
          simp [skyReducerSNode0LhsStoredState, layout, skyReducerSNode0Nat]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhs0Before)]
      rw [show (skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap =
          ((encodeHeapWithLayout layout s oracleVals).write
            (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
          simp [skyReducerSNode0TagStoredState, skyReducerSXYZLoadedState, skyReducerSXYLoadedState,
            skyReducerSXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
            skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
            encodeExecStateWithLayout, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
            skyReducerSNode0Nat, layout]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTag0Before)]
      exact hRefsBaseRead
    simpa [layout] using
      (readNatArray?_append_one_at_end
        (heap := (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap)
        (base := layout.refsBase)
        (count := s.nodeCount)
        (xs := s.oracleRefs)
        (a := 0)
        hRefsBeforeNode0)
  have hRefsNode1 :
      readNatArray? (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap
        layout.refsBase (s.nodeCount + 2) =
          some ((s.oracleRefs.push 0).push 0) := by
    rw [show (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.refsBase + s.nodeCount + 1) (.int 0)) by
        simp [skyReducerSNode1RefStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
    have hRefsBeforeNode1 :
        readNatArray? (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap
          layout.refsBase (s.nodeCount + 1) =
            some (s.oracleRefs.push 0) := by
      rw [show (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap =
          (((skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap).write
            (layout.rhsBase + s.nodeCount + 1) (skyReducerSZVal s hstack)) by
          simp [skyReducerSNode1RhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hRhs1Before)]
      rw [show (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap =
          (((skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap).write
            (layout.lhsBase + s.nodeCount + 1) (skyReducerSYVal s hstack)) by
          simp [skyReducerSNode1LhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhs1Before)]
      rw [show (skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap =
          (((skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap).write
            (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
          simp [skyReducerSNode1TagStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
      rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTag1Before)]
      exact hRefsNode0
    simpa [layout] using
      (readNatArray?_append_one_at_end
        (heap := (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap)
        (base := layout.refsBase)
        (count := s.nodeCount + 1)
        (xs := s.oracleRefs.push 0)
        (a := 0)
        hRefsBeforeNode1)
  rw [show (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 2) (.int 0)) by
      simp [skyReducerSNode2RefStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  have hRefsBeforeNode2 :
      readNatArray? (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap
        layout.refsBase (s.nodeCount + 2) =
          some ((s.oracleRefs.push 0).push 0) := by
    rw [show (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap).write
          (layout.rhsBase + s.nodeCount + 2) (skyReducerSNode1Val s)) by
        simp [skyReducerSNode2RhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hRhs2Before)]
    rw [show (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap).write
          (layout.lhsBase + s.nodeCount + 2) (skyReducerSNode0Val s)) by
        simp [skyReducerSNode2LhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hLhs2Before)]
    rw [show (skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap =
        (((skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap).write
          (layout.tagsBase + s.nodeCount + 2) (.int (NodeTag.code .app))) by
        simp [skyReducerSNode2TagStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
    rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hTag2Before)]
    exact hRefsNode1
  simpa [layout] using
    (readNatArray?_append_one_at_end
      (heap := (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap)
      (base := layout.refsBase)
      (count := s.nodeCount + 2)
      (xs := (s.oracleRefs.push 0).push 0)
      (a := 0)
      hRefsBeforeNode2)

theorem readStack_skyReducerSCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) (hcap : s.nodeCount + 3 ≤ s.maxNodes) :
    readNatArray? (skyReducerSCommittedState s oracleVals hfocus hstack).heap
      (layoutForState s oracleVals).stackBase (s.stack.length - 3) =
        some ((s.stack.drop 3).reverse.toArray) := by
  let layout := layoutForState s oracleVals
  have hStackNodeCount :
      layout.stackBase + (s.stack.length - 3) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackStackSize :
      layout.stackBase + (s.stack.length - 3) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackFocus :
      layout.stackBase + (s.stack.length - 3) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRefs2 :
      layout.refsBase + s.nodeCount + 2 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRhs2 :
      layout.rhsBase + s.nodeCount + 2 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackLhs2 :
      layout.lhsBase + s.nodeCount + 2 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackTag2 :
      layout.tagsBase + s.nodeCount + 2 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRefs1 :
      layout.refsBase + s.nodeCount + 1 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRhs1 :
      layout.rhsBase + s.nodeCount + 1 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackLhs1 :
      layout.lhsBase + s.nodeCount + 1 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackTag1 :
      layout.tagsBase + s.nodeCount + 1 < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRefs0 :
      layout.refsBase + s.nodeCount < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackRhs0 :
      layout.rhsBase + s.nodeCount < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackLhs0 :
      layout.lhsBase + s.nodeCount < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackTag0 :
      layout.tagsBase + s.nodeCount < layout.stackBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show (skyReducerSCommittedState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap).write
        layout.nodeCountBase (.int (Int.ofNat (s.nodeCount + 3)))) by
      simp [skyReducerSCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [show (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).heap =
      (((skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 3)))) by
      simp [skyReducerSCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [show (skyReducerSCommittedFocusState s oracleVals hfocus hstack).heap =
      (((skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap).write
        layout.focusBase (skyReducerSNode2Val s)) by
      simp [skyReducerSCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  rw [show (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).heap =
      (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap by
      simp [skyReducerSStackSizeUpdatedState, skyReducerSNodeCountUpdatedState,
        skyReducerSFocusUpdatedState]]
  rw [show (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 2) (.int 0)) by
      simp [skyReducerSNode2RefStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRefs2)]
  rw [show (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 2) (skyReducerSNode1Val s)) by
      simp [skyReducerSNode2RhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRhs2)]
  rw [show (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount + 2) (skyReducerSNode0Val s)) by
      simp [skyReducerSNode2LhsStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackLhs2)]
  rw [show (skyReducerSNode2TagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 2) (.int (NodeTag.code .app))) by
      simp [skyReducerSNode2TagStoredState, layout, skyReducerSNode2Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackTag2)]
  rw [show (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount + 1) (.int 0)) by
      simp [skyReducerSNode1RefStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRefs1)]
  rw [show (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount + 1) (skyReducerSZVal s hstack)) by
      simp [skyReducerSNode1RhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRhs1)]
  rw [show (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount + 1) (skyReducerSYVal s hstack)) by
      simp [skyReducerSNode1LhsStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackLhs1)]
  rw [show (skyReducerSNode1TagStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap).write
        (layout.tagsBase + s.nodeCount + 1) (.int (NodeTag.code .app))) by
      simp [skyReducerSNode1TagStoredState, layout, skyReducerSNode1Nat, Nat.add_assoc]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackTag1)]
  rw [show (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.refsBase + s.nodeCount) (.int 0)) by
      simp [skyReducerSNode0RefStoredState, layout, skyReducerSNode0Nat]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRefs0)]
  rw [show (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap).write
        (layout.rhsBase + s.nodeCount) (skyReducerSZVal s hstack)) by
      simp [skyReducerSNode0RhsStoredState, layout, skyReducerSNode0Nat]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackRhs0)]
  rw [show (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).heap =
      (((skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap).write
        (layout.lhsBase + s.nodeCount) (skyReducerSXVal s hstack)) by
      simp [skyReducerSNode0LhsStoredState, layout, skyReducerSNode0Nat]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackLhs0)]
  rw [show (skyReducerSNode0TagStoredState s oracleVals hfocus hstack).heap =
      ((encodeHeapWithLayout layout s oracleVals).write
        (layout.tagsBase + s.nodeCount) (.int (NodeTag.code .app))) by
      simp [skyReducerSNode0TagStoredState, skyReducerSXYZLoadedState, skyReducerSXYLoadedState,
        skyReducerSXLoadedState, skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
        skyReducerStackSizeLoadedState, skyReducerFocusLoadedState, skyReducerEntry,
        encodeExecStateWithLayout, updateVar_heap, HeytingLean.LeanCP.enterBlockState_heap,
        skyReducerSNode0Nat, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inl hStackTag0)]
  rw [show encodeHeapWithLayout layout s oracleVals =
      ((((encodeStackWithLayout layout s oracleVals).write layout.focusBase (.int (Int.ofNat s.focus))).write
        layout.stackSizeBase (.int (Int.ofNat s.stack.length))).write
        layout.nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [encodeHeapWithLayout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  cases hs : s.stack with
  | nil =>
      have : False := by
        simpa [hs] using hstack
      contradiction
  | cons x xs =>
      cases xs with
      | nil =>
          have : False := by
            simpa [hs] using hstack
          contradiction
      | cons y ys =>
          cases ys with
          | nil =>
              have : False := by
                simpa [hs] using hstack
              contradiction
          | cons z rest =>
              have hRev : (x :: y :: z :: rest).reverse = rest.reverse ++ [z, y, x] := by
                simp
              rw [show encodeStackWithLayout layout s oracleVals =
                  writeNatList (encodeOracleValuesWithLayout layout s oracleVals)
                    layout.stackBase ((x :: y :: z :: rest).reverse) by
                  simp [encodeStackWithLayout, hs]]
              rw [hRev, writeNatList_append]
              have hSuffix :
                  layout.stackBase + rest.length ≤ layout.stackBase + rest.reverse.length := by
                simp
              have hRead :
                  readNatArray?
                    (writeNatList
                      (writeNatList (encodeOracleValuesWithLayout layout s oracleVals) layout.stackBase
                        rest.reverse)
                      (layout.stackBase + rest.reverse.length) [z, y, x])
                    layout.stackBase rest.length =
                      some (rest.reverse.toArray) := by
                rw [readNatArray?_writeNatList_otherRange _ _ _ layout.stackBase rest.length hSuffix]
                simpa [layout, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  (readNatArray?_writeNatList
                    (heap := encodeOracleValuesWithLayout layout s oracleVals)
                    (base := layout.stackBase) (xs := rest.reverse))
              simpa [hs] using hRead

theorem decodeKernelState?_skyReducerSCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (skyReducerSCommittedState s oracleVals hfocus hstack) =
        some (skyReducerSNextState s hstack) := by
  rw [decodeKernelState?]
  rw [readFocus_skyReducerSCommittedState]
  rw [readStackSize_skyReducerSCommittedState]
  rw [readNodeCount_skyReducerSCommittedState]
  simp [skyReducerSNextState]
  rw [readTags_skyReducerSCommittedState s oracleVals hwf hfocus hstack hcap]
  rw [readLhs_skyReducerSCommittedState s oracleVals hwf hfocus hstack hcap]
  rw [readRhs_skyReducerSCommittedState s oracleVals hwf hfocus hstack hcap]
  rw [readOracleRefs_skyReducerSCommittedState s oracleVals hwf hfocus hstack hcap]
  rw [readStack_skyReducerSCommittedState s oracleVals hfocus hstack hcap]
  simp [skyReducerSNextState]
theorem decodeKernelState?_skyReducerKCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (skyReducerKCommittedState s oracleVals hfocus hstack) =
        some { s with
          focus := s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩
          stack := s.stack.drop 2 } := by
  rw [decodeKernelState?]
  rw [readFocus_skyReducerKCommittedState]
  rw [readStackSize_skyReducerKCommittedState]
  rw [readNodeCount_skyReducerKCommittedState]
  simp
  rw [readTags_skyReducerKCommittedState s oracleVals hwf hfocus hstack]
  rw [readLhs_skyReducerKCommittedState s oracleVals hwf hfocus hstack]
  rw [readRhs_skyReducerKCommittedState s oracleVals hwf hfocus hstack]
  rw [readOracleRefs_skyReducerKCommittedState s oracleVals hwf hfocus hstack]
  rw [readStack_skyReducerKCommittedState]
  simp

theorem runLoweredStep?_k
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length)
    (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    runLoweredStep? s oracleVals =
      some (.progress, { s with
        focus := s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩
        stack := s.stack.drop 2 }) := by
  have hwf' :
      ({ s with
          focus := s.stack.get ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hstack⟩
          stack := s.stack.drop 2 }).WellFormed := by
    rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, _⟩
    have hnodes' : s.tags.size ≤ s.maxNodes := by
      simpa [State.nodeCount] using hnodes
    exact ⟨hlhs, hrhs, hrefs, hnodes', trivial⟩
  simp [runLoweredStep?]
  rw [execStmt_kPath_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack hk]
  simp [StepStatus.ofCode?, StepStatus.code]
  rw [decodeKernelState?_skyReducerKCommittedState]
  simp [StepStatus.ofCode?, StepStatus.code]
  all_goals
    first
    | exact hwf'
    | exact hwf

theorem readFocus_skyReducerOracleCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatCell?
        (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap
        (layoutForState s oracleVals).focusBase =
      some (skyReducerOracleTargetNat s oracleVals hwf hfocus hstack) := by
  have hFocusNeNodeCountBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hFocusNeStackSizeBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
  rw [show
      (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerOracleCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeNodeCountBase]
  rw [show
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerOracleCommittedStackSizeState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeStackSizeBase]
  simpa [skyReducerOracleCommittedFocusState, skyReducerOracleTargetVal]
    using (readNatCell?_write_same
      (heap := (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap)
      (addr := (layoutForState s oracleVals).focusBase)
      (n := skyReducerOracleTargetNat s oracleVals hwf hfocus hstack))

theorem readStackSize_skyReducerOracleCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatCell?
        (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap
        (layoutForState s oracleVals).stackSizeBase =
      some (s.stack.length - 2) := by
  have hStackSizeNeNodeCountBase :
      (layoutForState s oracleVals).stackSizeBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
  rw [show
      (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerOracleCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hStackSizeNeNodeCountBase]
  simpa [skyReducerOracleCommittedStackSizeState]
    using (readNatCell?_write_same
      (heap := (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap)
      (addr := (layoutForState s oracleVals).stackSizeBase)
      (n := s.stack.length - 2))

theorem readNodeCount_skyReducerOracleCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatCell?
        (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap
        (layoutForState s oracleVals).nodeCountBase =
      some s.nodeCount := by
  simpa [skyReducerOracleCommittedState]
    using (readNatCell?_write_same
      (heap := (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap)
      (addr := (layoutForState s oracleVals).nodeCountBase)
      (n := s.nodeCount))

theorem readTags_skyReducerOracleCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readIntArray?
        (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap
        (layoutForState s oracleVals).tagsBase s.nodeCount =
      some s.tags := by
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hTagsNodeCount :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsStackSize :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsFocus :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show
      (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerOracleCommittedState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsNodeCount)]
  rw [show
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerOracleCommittedStackSizeState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsStackSize)]
  rw [show
      (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).focusBase
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)) by
      simp [skyReducerOracleCommittedFocusState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsFocus)]
  simpa [skyReducerOracleStackSizeUpdatedState, skyReducerOracleFocusUpdatedState,
    skyReducerOracleXYRefLoadedState, skyReducerOracleXYLoadedState, skyReducerOracleXLoadedState,
    skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout]
    using readTags_encodeHeapWithLayout s oracleVals hnodes

theorem readLhs_skyReducerOracleCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatArray?
        (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap
        (layoutForState s oracleVals).lhsBase s.nodeCount =
      some s.lhs := by
  have hlhs : s.lhs.size = s.nodeCount := hwf.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hLhsNodeCount :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsStackSize :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsFocus :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show
      (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerOracleCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsNodeCount)]
  rw [show
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerOracleCommittedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsStackSize)]
  rw [show
      (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).focusBase
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)) by
      simp [skyReducerOracleCommittedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsFocus)]
  simpa [skyReducerOracleStackSizeUpdatedState, skyReducerOracleFocusUpdatedState,
    skyReducerOracleXYRefLoadedState, skyReducerOracleXYLoadedState, skyReducerOracleXLoadedState,
    skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, hlhs]
    using readLhs_encodeHeapWithLayout s oracleVals hlhs hnodes

theorem readRhs_skyReducerOracleCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatArray?
        (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap
        (layoutForState s oracleVals).rhsBase s.nodeCount =
      some s.rhs := by
  have hrhs : s.rhs.size = s.nodeCount := hwf.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hRhsNodeCount :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsStackSize :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsFocus :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show
      (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerOracleCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsNodeCount)]
  rw [show
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerOracleCommittedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsStackSize)]
  rw [show
      (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).focusBase
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)) by
      simp [skyReducerOracleCommittedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsFocus)]
  simpa [skyReducerOracleStackSizeUpdatedState, skyReducerOracleFocusUpdatedState,
    skyReducerOracleXYRefLoadedState, skyReducerOracleXYLoadedState, skyReducerOracleXLoadedState,
    skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, hrhs]
    using readRhs_encodeHeapWithLayout s oracleVals hrhs hnodes

theorem readOracleRefs_skyReducerOracleCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatArray?
        (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap
        (layoutForState s oracleVals).refsBase s.nodeCount =
      some s.oracleRefs := by
  have hrefs : s.oracleRefs.size = s.nodeCount := hwf.2.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hRefsNodeCount :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsStackSize :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsFocus :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show
      (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerOracleCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsNodeCount)]
  rw [show
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerOracleCommittedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsStackSize)]
  rw [show
      (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        (layoutForState s oracleVals).focusBase
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)) by
      simp [skyReducerOracleCommittedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsFocus)]
  simpa [skyReducerOracleStackSizeUpdatedState, skyReducerOracleFocusUpdatedState,
    skyReducerOracleXYRefLoadedState, skyReducerOracleXYLoadedState, skyReducerOracleXLoadedState,
    skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, hrefs]
    using readOracleRefs_encodeHeapWithLayout s oracleVals hrefs hnodes

theorem readStack_skyReducerOracleCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    readNatArray?
        (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap
        (layoutForState s oracleVals).stackBase (s.stack.length - 2) =
      some ((s.stack.drop 2).reverse.toArray) := by
  let layout := layoutForState s oracleVals
  have hStackNodeCount :
      layout.stackBase + (s.stack.length - 2) ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackStackSize :
      layout.stackBase + (s.stack.length - 2) ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackFocus :
      layout.stackBase + (s.stack.length - 2) ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  rw [show
      (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        layout.nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerOracleCommittedState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [show
      (skyReducerOracleCommittedStackSizeState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        layout.stackSizeBase (.int (Int.ofNat (s.stack.length - 2)))) by
      simp [skyReducerOracleCommittedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [show
      (skyReducerOracleCommittedFocusState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      (((skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack
          (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap).write
        layout.focusBase (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)) by
      simp [skyReducerOracleCommittedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  rw [show
      (skyReducerOracleStackSizeUpdatedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)).heap =
      encodeHeapWithLayout layout s oracleVals by
      simp [skyReducerOracleStackSizeUpdatedState, skyReducerOracleFocusUpdatedState,
        skyReducerOracleXYRefLoadedState, skyReducerOracleXYLoadedState, skyReducerOracleXLoadedState,
        skyReducerAppTagLoadedState, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
        skyReducerFocusLoadedState, skyReducerEntry, layout, encodeExecStateWithLayout]]
  rw [show encodeHeapWithLayout layout s oracleVals =
      ((((encodeStackWithLayout layout s oracleVals).write layout.focusBase (.int (Int.ofNat s.focus))).write
        layout.stackSizeBase (.int (Int.ofNat s.stack.length))).write
        layout.nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [encodeHeapWithLayout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  cases hs : s.stack with
  | nil =>
      have : False := by
        simpa [hs] using hstack
      contradiction
  | cons x xs =>
      cases xs with
      | nil =>
          have : False := by
            simpa [hs] using hstack
          contradiction
      | cons y rest =>
          have hRev : (x :: y :: rest).reverse = rest.reverse ++ [y, x] := by
            simp
          rw [show encodeStackWithLayout layout s oracleVals =
              writeNatList (encodeOracleValuesWithLayout layout s oracleVals)
                layout.stackBase ((x :: y :: rest).reverse) by
              simp [encodeStackWithLayout, hs]]
          rw [hRev, writeNatList_append]
          have hSuffix :
              layout.stackBase + rest.length ≤ layout.stackBase + rest.reverse.length := by
            simp
          have hRead :
              readNatArray?
                (writeNatList
                  (writeNatList (encodeOracleValuesWithLayout layout s oracleVals) layout.stackBase
                    rest.reverse)
                  (layout.stackBase + rest.reverse.length) [y, x])
                layout.stackBase rest.length =
                  some (rest.reverse.toArray) := by
            rw [readNatArray?_writeNatList_otherRange _ _ _ layout.stackBase rest.length hSuffix]
            simpa [layout, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (readNatArray?_writeNatList
                (heap := encodeOracleValuesWithLayout layout s oracleVals)
                (base := layout.stackBase) (xs := rest.reverse))
          simpa using hRead

theorem decodeKernelState?_skyReducerOracleCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (skyReducerOracleCommittedState s oracleVals hwf hfocus hstack
        (skyReducerOracleTargetVal s oracleVals hwf hfocus hstack)) =
        some { s with
          focus := skyReducerOracleTargetNat s oracleVals hwf hfocus hstack
          stack := s.stack.drop 2 } := by
  rw [decodeKernelState?]
  rw [readFocus_skyReducerOracleCommittedState]
  rw [readStackSize_skyReducerOracleCommittedState]
  rw [readNodeCount_skyReducerOracleCommittedState]
  simp
  rw [readTags_skyReducerOracleCommittedState s oracleVals hwf hfocus hstack]
  rw [readLhs_skyReducerOracleCommittedState s oracleVals hwf hfocus hstack]
  rw [readRhs_skyReducerOracleCommittedState s oracleVals hwf hfocus hstack]
  rw [readOracleRefs_skyReducerOracleCommittedState s oracleVals hwf hfocus hstack]
  rw [readStack_skyReducerOracleCommittedState s oracleVals hwf hfocus hstack]
  simp

theorem runLoweredStep?_oracle
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 2 ≤ s.stack.length)
    (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    runLoweredStep? s oracleVals =
      some (.progress, { s with
        focus := skyReducerOracleTargetNat s oracleVals hwf hfocus hstack
        stack := s.stack.drop 2 }) := by
  have hwf' :
      ({ s with
          focus := skyReducerOracleTargetNat s oracleVals hwf hfocus hstack
          stack := s.stack.drop 2 }).WellFormed := by
    rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, _⟩
    have hnodes' : s.tags.size ≤ s.maxNodes := by
      simpa [State.nodeCount] using hnodes
    exact ⟨hlhs, hrhs, hrefs, hnodes', trivial⟩
  simp [runLoweredStep?]
  rw [execStmt_oraclePath_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack horacleTag]
  simp [StepStatus.ofCode?, StepStatus.code]
  rw [decodeKernelState?_skyReducerOracleCommittedState]
  simp [StepStatus.ofCode?, StepStatus.code]
  all_goals
    first
    | exact hwf'
    | exact hwf

theorem decodeKernelState?_encodeExecStateWithLayout (s : State) (oracleVals : Array Int)
    (hwf : s.WellFormed) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) = some s := by
  rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, _hstack⟩
  simp [decodeKernelState?, encodeExecStateWithLayout,
    readFocus_encodeHeapWithLayout, readStackSize_encodeHeapWithLayout,
    readNodeCount_encodeHeapWithLayout, readTags_encodeHeapWithLayout,
    readLhs_encodeHeapWithLayout, readRhs_encodeHeapWithLayout,
    readOracleRefs_encodeHeapWithLayout, readStack_encodeHeapWithLayout,
    hlhs, hrhs, hrefs, hnodes]

theorem decodeKernelState?_encodeExecState (s : State) (oracleVals : Array Int)
    (hwf : s.WellFormed) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals) (encodeExecState s oracleVals) = some s := by
  simpa [encodeExecState] using decodeKernelState?_encodeExecStateWithLayout s oracleVals hwf

theorem readFocus_skyReducerUnchangedCommittedState
    (s : State) (oracleVals : Array Int) :
    readNatCell? (skyReducerUnchangedCommittedState s oracleVals).heap
      (layoutForState s oracleVals).focusBase = some s.focus := by
  have hFocusNeNodeCountBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hFocusNeStackSizeBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerUnchangedCommittedState s oracleVals).heap =
      (((skyReducerUnchangedStackSizeCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerUnchangedCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeNodeCountBase]
  rw [show (skyReducerUnchangedStackSizeCommitState s oracleVals).heap =
      (((skyReducerUnchangedFocusCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerUnchangedStackSizeCommitState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeStackSizeBase]
  simpa [skyReducerUnchangedFocusCommitState]
    using (readNatCell?_write_same
      (heap := (skyReducerScalarsLoadedState s oracleVals).heap)
      (addr := (layoutForState s oracleVals).focusBase)
      (n := s.focus))

theorem readStackSize_skyReducerUnchangedCommittedState
    (s : State) (oracleVals : Array Int) :
    readNatCell? (skyReducerUnchangedCommittedState s oracleVals).heap
      (layoutForState s oracleVals).stackSizeBase = some s.stack.length := by
  have hStackSizeNeNodeCountBase :
      (layoutForState s oracleVals).stackSizeBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerUnchangedCommittedState s oracleVals).heap =
      (((skyReducerUnchangedStackSizeCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerUnchangedCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hStackSizeNeNodeCountBase]
  simpa [skyReducerUnchangedStackSizeCommitState]
    using (readNatCell?_write_same
      (heap := (skyReducerUnchangedFocusCommitState s oracleVals).heap)
      (addr := (layoutForState s oracleVals).stackSizeBase)
      (n := s.stack.length))

theorem readNodeCount_skyReducerUnchangedCommittedState
    (s : State) (oracleVals : Array Int) :
    readNatCell? (skyReducerUnchangedCommittedState s oracleVals).heap
      (layoutForState s oracleVals).nodeCountBase = some s.nodeCount := by
  simpa [skyReducerUnchangedCommittedState]
    using (readNatCell?_write_same
      (heap := (skyReducerUnchangedStackSizeCommitState s oracleVals).heap)
      (addr := (layoutForState s oracleVals).nodeCountBase)
      (n := s.nodeCount))

theorem readTags_skyReducerUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    readIntArray? (skyReducerUnchangedCommittedState s oracleVals).heap
      (layoutForState s oracleVals).tagsBase s.nodeCount = some s.tags := by
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hTagsNodeCount :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsStackSize :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsFocus :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerUnchangedCommittedState s oracleVals).heap =
      (((skyReducerUnchangedStackSizeCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerUnchangedCommittedState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsNodeCount)]
  rw [show (skyReducerUnchangedStackSizeCommitState s oracleVals).heap =
      (((skyReducerUnchangedFocusCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerUnchangedStackSizeCommitState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsStackSize)]
  rw [show (skyReducerUnchangedFocusCommitState s oracleVals).heap =
      (((skyReducerScalarsLoadedState s oracleVals).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerUnchangedFocusCommitState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsFocus)]
  simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout]
    using readTags_encodeHeapWithLayout s oracleVals hnodes

theorem readLhs_skyReducerUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    readNatArray? (skyReducerUnchangedCommittedState s oracleVals).heap
      (layoutForState s oracleVals).lhsBase s.nodeCount = some s.lhs := by
  have hlhs : s.lhs.size = s.nodeCount := hwf.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hLhsNodeCount :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsStackSize :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsFocus :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerUnchangedCommittedState s oracleVals).heap =
      (((skyReducerUnchangedStackSizeCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerUnchangedCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsNodeCount)]
  rw [show (skyReducerUnchangedStackSizeCommitState s oracleVals).heap =
      (((skyReducerUnchangedFocusCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerUnchangedStackSizeCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsStackSize)]
  rw [show (skyReducerUnchangedFocusCommitState s oracleVals).heap =
      (((skyReducerScalarsLoadedState s oracleVals).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerUnchangedFocusCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsFocus)]
  simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, hlhs]
    using readLhs_encodeHeapWithLayout s oracleVals hlhs hnodes

theorem readRhs_skyReducerUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    readNatArray? (skyReducerUnchangedCommittedState s oracleVals).heap
      (layoutForState s oracleVals).rhsBase s.nodeCount = some s.rhs := by
  have hrhs : s.rhs.size = s.nodeCount := hwf.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hRhsNodeCount :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsStackSize :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsFocus :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerUnchangedCommittedState s oracleVals).heap =
      (((skyReducerUnchangedStackSizeCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerUnchangedCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsNodeCount)]
  rw [show (skyReducerUnchangedStackSizeCommitState s oracleVals).heap =
      (((skyReducerUnchangedFocusCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerUnchangedStackSizeCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsStackSize)]
  rw [show (skyReducerUnchangedFocusCommitState s oracleVals).heap =
      (((skyReducerScalarsLoadedState s oracleVals).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerUnchangedFocusCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsFocus)]
  simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, hrhs]
    using readRhs_encodeHeapWithLayout s oracleVals hrhs hnodes

theorem readOracleRefs_skyReducerUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    readNatArray? (skyReducerUnchangedCommittedState s oracleVals).heap
      (layoutForState s oracleVals).refsBase s.nodeCount = some s.oracleRefs := by
  have hrefs : s.oracleRefs.size = s.nodeCount := hwf.2.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hRefsNodeCount :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsStackSize :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsFocus :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerUnchangedCommittedState s oracleVals).heap =
      (((skyReducerUnchangedStackSizeCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerUnchangedCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsNodeCount)]
  rw [show (skyReducerUnchangedStackSizeCommitState s oracleVals).heap =
      (((skyReducerUnchangedFocusCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerUnchangedStackSizeCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsStackSize)]
  rw [show (skyReducerUnchangedFocusCommitState s oracleVals).heap =
      (((skyReducerScalarsLoadedState s oracleVals).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerUnchangedFocusCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsFocus)]
  simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, hrefs]
    using readOracleRefs_encodeHeapWithLayout s oracleVals hrefs hnodes

theorem readStack_skyReducerUnchangedCommittedState
    (s : State) (oracleVals : Array Int) :
    readNatArray? (skyReducerUnchangedCommittedState s oracleVals).heap
      (layoutForState s oracleVals).stackBase s.stack.length = some s.stack.reverse.toArray := by
  have hStackNodeCount :
      (layoutForState s oracleVals).stackBase + s.stack.length ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hStackStackSize :
      (layoutForState s oracleVals).stackBase + s.stack.length ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hStackFocus :
      (layoutForState s oracleVals).stackBase + s.stack.length ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerUnchangedCommittedState s oracleVals).heap =
      (((skyReducerUnchangedStackSizeCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerUnchangedCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [show (skyReducerUnchangedStackSizeCommitState s oracleVals).heap =
      (((skyReducerUnchangedFocusCommitState s oracleVals).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerUnchangedStackSizeCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [show (skyReducerUnchangedFocusCommitState s oracleVals).heap =
      (((skyReducerScalarsLoadedState s oracleVals).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerUnchangedFocusCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout]
    using readStack_encodeHeapWithLayout s oracleVals

theorem decodeKernelState?_skyReducerUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (skyReducerUnchangedCommittedState s oracleVals) = some s := by
  have hlhs : s.lhs.size = s.nodeCount := hwf.1
  have hrhs : s.rhs.size = s.nodeCount := hwf.2.1
  have hrefs : s.oracleRefs.size = s.nodeCount := hwf.2.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  unfold decodeKernelState?
  simp [readFocus_skyReducerUnchangedCommittedState,
    readStackSize_skyReducerUnchangedCommittedState,
    readNodeCount_skyReducerUnchangedCommittedState,
    readStack_skyReducerUnchangedCommittedState]
  rw [readTags_skyReducerUnchangedCommittedState s oracleVals hwf]
  rw [readLhs_skyReducerUnchangedCommittedState s oracleVals hwf]
  rw [readRhs_skyReducerUnchangedCommittedState s oracleVals hwf]
  rw [readOracleRefs_skyReducerUnchangedCommittedState s oracleVals hwf]
  simp [hlhs, hrhs, hrefs, hnodes]

theorem readFocus_skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    readNatCell? (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap
      (layoutForState s oracleVals).focusBase = some s.focus := by
  have hFocusNeNodeCountBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hFocusNeStackSizeBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerTagLoadedUnchangedCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeNodeCountBase]
  rw [show (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerTagLoadedUnchangedStackSizeCommitState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeStackSizeBase]
  simpa [skyReducerTagLoadedUnchangedFocusCommitState]
    using (readNatCell?_write_same
      (heap := (skyReducerAppTagLoadedState s oracleVals hfocus).heap)
      (addr := (layoutForState s oracleVals).focusBase)
      (n := s.focus))

theorem readStackSize_skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    readNatCell? (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap
      (layoutForState s oracleVals).stackSizeBase = some s.stack.length := by
  have hStackSizeNeNodeCountBase :
      (layoutForState s oracleVals).stackSizeBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerTagLoadedUnchangedCommittedState]]
  rw [readNatCell?_write_other _ _ _ _ hStackSizeNeNodeCountBase]
  simpa [skyReducerTagLoadedUnchangedStackSizeCommitState]
    using (readNatCell?_write_same
      (heap := (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap)
      (addr := (layoutForState s oracleVals).stackSizeBase)
      (n := s.stack.length))

theorem readNodeCount_skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    readNatCell? (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap
      (layoutForState s oracleVals).nodeCountBase = some s.nodeCount := by
  simpa [skyReducerTagLoadedUnchangedCommittedState]
    using (readNatCell?_write_same
      (heap := (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap)
      (addr := (layoutForState s oracleVals).nodeCountBase)
      (n := s.nodeCount))

theorem readTags_skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    readIntArray? (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap
      (layoutForState s oracleVals).tagsBase s.nodeCount = some s.tags := by
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hTagsNodeCount :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsStackSize :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsFocus :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerTagLoadedUnchangedCommittedState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsNodeCount)]
  rw [show (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerTagLoadedUnchangedStackSizeCommitState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsStackSize)]
  rw [show (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap =
      (((skyReducerAppTagLoadedState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerTagLoadedUnchangedFocusCommitState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsFocus)]
  simpa [skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
    skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout]
    using readTags_encodeHeapWithLayout s oracleVals hnodes

theorem readLhs_skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    readNatArray? (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap
      (layoutForState s oracleVals).lhsBase s.nodeCount = some s.lhs := by
  have hlhs : s.lhs.size = s.nodeCount := hwf.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hLhsNodeCount :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsStackSize :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsFocus :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerTagLoadedUnchangedCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsNodeCount)]
  rw [show (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerTagLoadedUnchangedStackSizeCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsStackSize)]
  rw [show (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap =
      (((skyReducerAppTagLoadedState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerTagLoadedUnchangedFocusCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsFocus)]
  simpa [skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
    skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout, hlhs]
    using readLhs_encodeHeapWithLayout s oracleVals hlhs hnodes

theorem readRhs_skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    readNatArray? (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap
      (layoutForState s oracleVals).rhsBase s.nodeCount = some s.rhs := by
  have hrhs : s.rhs.size = s.nodeCount := hwf.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hRhsNodeCount :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsStackSize :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsFocus :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerTagLoadedUnchangedCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsNodeCount)]
  rw [show (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerTagLoadedUnchangedStackSizeCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsStackSize)]
  rw [show (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap =
      (((skyReducerAppTagLoadedState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerTagLoadedUnchangedFocusCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsFocus)]
  simpa [skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
    skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout, hrhs]
    using readRhs_encodeHeapWithLayout s oracleVals hrhs hnodes

theorem readOracleRefs_skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    readNatArray? (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap
      (layoutForState s oracleVals).refsBase s.nodeCount = some s.oracleRefs := by
  have hrefs : s.oracleRefs.size = s.nodeCount := hwf.2.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hRefsNodeCount :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsStackSize :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsFocus :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerTagLoadedUnchangedCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsNodeCount)]
  rw [show (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerTagLoadedUnchangedStackSizeCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsStackSize)]
  rw [show (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap =
      (((skyReducerAppTagLoadedState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerTagLoadedUnchangedFocusCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsFocus)]
  simpa [skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
    skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout, hrefs]
    using readOracleRefs_encodeHeapWithLayout s oracleVals hrefs hnodes

theorem readStack_skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount) :
    readNatArray? (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap
      (layoutForState s oracleVals).stackBase s.stack.length = some s.stack.reverse.toArray := by
  have hStackNodeCount :
      (layoutForState s oracleVals).stackBase + s.stack.length ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hStackStackSize :
      (layoutForState s oracleVals).stackBase + s.stack.length ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hStackFocus :
      (layoutForState s oracleVals).stackBase + s.stack.length ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
  rw [show (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [skyReducerTagLoadedUnchangedCommittedState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [show (skyReducerTagLoadedUnchangedStackSizeCommitState s oracleVals hfocus).heap =
      (((skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [skyReducerTagLoadedUnchangedStackSizeCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [show (skyReducerTagLoadedUnchangedFocusCommitState s oracleVals hfocus).heap =
      (((skyReducerAppTagLoadedState s oracleVals hfocus).heap).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [skyReducerTagLoadedUnchangedFocusCommitState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  simpa [skyReducerAppTagLoadedState, skyReducerScalarsLoadedState,
    skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout]
    using readStack_encodeHeapWithLayout s oracleVals

theorem decodeKernelState?_skyReducerTagLoadedUnchangedCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (skyReducerTagLoadedUnchangedCommittedState s oracleVals hfocus) = some s := by
  have hlhs : s.lhs.size = s.nodeCount := hwf.1
  have hrhs : s.rhs.size = s.nodeCount := hwf.2.1
  have hrefs : s.oracleRefs.size = s.nodeCount := hwf.2.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  unfold decodeKernelState?
  simp [readFocus_skyReducerTagLoadedUnchangedCommittedState,
    readStackSize_skyReducerTagLoadedUnchangedCommittedState,
    readNodeCount_skyReducerTagLoadedUnchangedCommittedState,
    readStack_skyReducerTagLoadedUnchangedCommittedState]
  rw [readTags_skyReducerTagLoadedUnchangedCommittedState s oracleVals hwf hfocus]
  rw [readLhs_skyReducerTagLoadedUnchangedCommittedState s oracleVals hwf hfocus]
  rw [readRhs_skyReducerTagLoadedUnchangedCommittedState s oracleVals hwf hfocus]
  rw [readOracleRefs_skyReducerTagLoadedUnchangedCommittedState s oracleVals hwf hfocus]
  simp [hlhs, hrhs, hrefs, hnodes]

theorem decodeKernelState?_skyReducerScalarsLoadedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (skyReducerScalarsLoadedState s oracleVals) = some s := by
  simpa [skyReducerScalarsLoadedState_heap_eq_encodeHeapWithLayout] using
    decodeKernelState?_encodeExecStateWithLayout s oracleVals hwf

theorem decodeKernelState?_skyReducerScalarsCommittedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (skyReducerScalarsCommittedState s oracleVals) = some s := by
  simpa [skyReducerScalarsCommittedState, skyReducerScalarsLoadedState_heap_eq_encodeHeapWithLayout] using
    decodeKernelState?_encodeExecStateWithLayout s oracleVals hwf

theorem execStmt_focusOutOfRange_encodeExecState
    (s : State) (oracleVals : Array Int) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt 15 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerScalarsCommittedState s oracleVals)
            skyReducerLocals)) := by
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 14
          (SKYLowering.seqs
            [ .assign (.var "focus") (.deref (.var "focusPtr"))
            , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
            , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
            , .ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted) ])
          (enterBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            [ ("tag", .int)
            , ("focus", .int)
            , ("stackSize", .int)
            , ("nodeCount", .int)
            , ("x", .int)
            , ("y", .int)
            , ("z", .int)
            , ("ref", .int) ]) =
        some (.returned (.int StepStatus.halted.code)
          (skyReducerScalarsCommittedState s oracleVals)) := by
    have hentry :
        execStmt 14
            (.seq
              (.assign (.var "focus") (.deref (.var "focusPtr")))
              (.seq
                (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                (.seq
                  (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                  (.ite
                    (.binop .lt (.var "focus") (.var "nodeCount"))
                    (.seq
                      (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                      (switchMany (.var "tag")
                        [ (NodeTag.code .app, SKYLowering.appCase)
                        , (NodeTag.code .combK, SKYLowering.kCase)
                        , (NodeTag.code .combS, SKYLowering.sCase)
                        , (NodeTag.code .combY, SKYLowering.yCase)
                        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                        (SKYLowering.commitAndReturn .halted)))
                    (SKYLowering.commitAndReturn .halted)))))
            (skyReducerEntry s oracleVals) =
          some (.returned (.int StepStatus.halted.code)
            (skyReducerScalarsCommittedState s oracleVals)) := by
      rw [execStmt_focusOutOfRange_skyReducerEntry s oracleVals hfocus]
      exact execStmt_haltedCommit_skyReducerScalarsLoaded s oracleVals
    simpa [SKYLowering.seqs, skyReducerEntry, skyReducerLocals] using hentry
  rw [hbody]
  rfl

theorem execStmt_focusOutOfRange_encodeExecState_fuel
    (extra : Nat) (s : State) (oracleVals : Array Int) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt (15 + extra) SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerScalarsCommittedState s oracleVals)
            skyReducerLocals)) := by
  exact execStmt_fuel_mono
    (stmt := SKYLowering.skyReducerStepDecl.body)
    (st := encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
    (res := .returned (.int StepStatus.halted.code)
      (restoreBlockState
        (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
        (skyReducerScalarsCommittedState s oracleVals)
        skyReducerLocals))
    (extra := extra)
    (execStmt_focusOutOfRange_encodeExecState s oracleVals hfocus)

theorem execStmt_focusOutOfRange_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hfocus : ¬ s.focus < s.nodeCount) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerScalarsCommittedState s oracleVals)
            skyReducerLocals)) := by
  simpa using execStmt_focusOutOfRange_encodeExecState_fuel 385 s oracleVals hfocus

theorem readFocus_committedScalarsLoadedState
    (s : State) (oracleVals : Array Int) :
    readNatCell?
        (committedNodeCountState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount))).heap
        (layoutForState s oracleVals).focusBase =
      some s.focus := by
  have hFocusNeNodeCountBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hFocusNeStackSizeBase :
      (layoutForState s oracleVals).focusBase ≠ (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
  rw [show
      (committedNodeCountState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount))).heap =
      (((committedStackSizeState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [committedNodeCountState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeNodeCountBase]
  rw [show
      (committedStackSizeState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))).heap =
      (((committedFocusState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [committedStackSizeState]]
  rw [readNatCell?_write_other _ _ _ _ hFocusNeStackSizeBase]
  simpa using
    (readNatCell?_write_same
      (heap := (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals))
      (addr := (layoutForState s oracleVals).focusBase)
      (n := s.focus))

theorem readStackSize_committedScalarsLoadedState
    (s : State) (oracleVals : Array Int) :
    readNatCell?
        (committedNodeCountState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount))).heap
        (layoutForState s oracleVals).stackSizeBase =
      some s.stack.length := by
  have hStackSizeNeNodeCountBase :
      (layoutForState s oracleVals).stackSizeBase ≠ (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
  rw [show
      (committedNodeCountState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount))).heap =
      (((committedStackSizeState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [committedNodeCountState]]
  rw [readNatCell?_write_other _ _ _ _ hStackSizeNeNodeCountBase]
  simpa using
    (readNatCell?_write_same
      (heap := ((encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))))
      (addr := (layoutForState s oracleVals).stackSizeBase)
      (n := s.stack.length))

theorem readNodeCount_committedScalarsLoadedState
    (s : State) (oracleVals : Array Int) :
    readNatCell?
        (committedNodeCountState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount))).heap
        (layoutForState s oracleVals).nodeCountBase =
      some s.nodeCount := by
  simpa [committedNodeCountState, committedStackSizeState, committedFocusState,
    skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap] using
    (readNatCell?_write_same
      (heap := (((encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))))
      (addr := (layoutForState s oracleVals).nodeCountBase)
      (n := s.nodeCount))

theorem readTags_committedScalarsLoadedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    readIntArray?
        (committedNodeCountState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount))).heap
        (layoutForState s oracleVals).tagsBase s.nodeCount =
      some s.tags := by
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hTagsNodeCount :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsStackSize :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hTagsFocus :
      (layoutForState s oracleVals).tagsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show
      (committedNodeCountState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount))).heap =
      (((committedStackSizeState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [committedNodeCountState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsNodeCount)]
  rw [show
      (committedStackSizeState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))).heap =
      (((committedFocusState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [committedStackSizeState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsStackSize)]
  rw [show
      (committedFocusState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))).heap =
      ((skyReducerScalarsLoadedState s oracleVals).heap.write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [committedFocusState]]
  rw [readIntArray?_write_other _ _ _ _ _ (Or.inr hTagsFocus)]
  simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap] using
    readTags_encodeHeapWithLayout s oracleVals hnodes

theorem readLhs_committedScalarsLoadedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    readNatArray?
        (committedNodeCountState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount))).heap
        (layoutForState s oracleVals).lhsBase s.nodeCount =
      some s.lhs := by
  have hlhs : s.lhs.size = s.nodeCount := hwf.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hLhsNodeCount :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsStackSize :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hLhsFocus :
      (layoutForState s oracleVals).lhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show
      (committedNodeCountState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount))).heap =
      (((committedStackSizeState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [committedNodeCountState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsNodeCount)]
  rw [show
      (committedStackSizeState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))).heap =
      (((committedFocusState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [committedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsStackSize)]
  rw [show
      (committedFocusState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))).heap =
      ((skyReducerScalarsLoadedState s oracleVals).heap.write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [committedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hLhsFocus)]
  simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap] using
    readLhs_encodeHeapWithLayout s oracleVals hlhs hnodes

theorem readRhs_committedScalarsLoadedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    readNatArray?
        (committedNodeCountState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount))).heap
        (layoutForState s oracleVals).rhsBase s.nodeCount =
      some s.rhs := by
  have hrhs : s.rhs.size = s.nodeCount := hwf.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hRhsNodeCount :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsStackSize :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRhsFocus :
      (layoutForState s oracleVals).rhsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show
      (committedNodeCountState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount))).heap =
      (((committedStackSizeState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [committedNodeCountState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsNodeCount)]
  rw [show
      (committedStackSizeState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))).heap =
      (((committedFocusState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [committedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsStackSize)]
  rw [show
      (committedFocusState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))).heap =
      ((skyReducerScalarsLoadedState s oracleVals).heap.write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [committedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRhsFocus)]
  simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap] using
    readRhs_encodeHeapWithLayout s oracleVals hrhs hnodes

theorem readOracleRefs_committedScalarsLoadedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    readNatArray?
        (committedNodeCountState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount))).heap
        (layoutForState s oracleVals).refsBase s.nodeCount =
      some s.oracleRefs := by
  have hrefs : s.oracleRefs.size = s.nodeCount := hwf.2.2.1
  have hnodes : s.nodeCount ≤ s.maxNodes := hwf.2.2.2.1
  have hRefsNodeCount :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).nodeCountBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsStackSize :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).stackSizeBase := by
    simp [layoutForState, layoutFor]
    omega
  have hRefsFocus :
      (layoutForState s oracleVals).refsBase + s.nodeCount ≤
        (layoutForState s oracleVals).focusBase := by
    simp [layoutForState, layoutFor]
    omega
  rw [show
      (committedNodeCountState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount))).heap =
      (((committedStackSizeState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))).heap).write
        (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [committedNodeCountState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsNodeCount)]
  rw [show
      (committedStackSizeState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))).heap =
      (((committedFocusState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))).heap).write
        (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [committedStackSizeState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsStackSize)]
  rw [show
      (committedFocusState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))).heap =
      ((skyReducerScalarsLoadedState s oracleVals).heap.write
        (layoutForState s oracleVals).focusBase (.int (Int.ofNat s.focus))) by
      simp [committedFocusState]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hRefsFocus)]
  simpa [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState, skyReducerFocusLoadedState,
    skyReducerEntry, encodeExecStateWithLayout, updateVar_heap, enterBlockState_heap] using
    readOracleRefs_encodeHeapWithLayout s oracleVals hrefs hnodes

theorem readStack_committedScalarsLoadedState
    (s : State) (oracleVals : Array Int) :
    readNatArray?
        (committedNodeCountState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount))).heap
        (layoutForState s oracleVals).stackBase s.stack.length =
      some s.stack.reverse.toArray := by
  let layout := layoutForState s oracleVals
  have hStackNodeCount :
      layout.stackBase + s.stack.length ≤ layout.nodeCountBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackStackSize :
      layout.stackBase + s.stack.length ≤ layout.stackSizeBase := by
    simp [layout, layoutForState, layoutFor]
    omega
  have hStackFocus :
      layout.stackBase + s.stack.length ≤ layout.focusBase := by
    simp [layout, layoutForState, layoutFor]
  rw [show
      (committedNodeCountState
        (skyReducerScalarsLoadedState s oracleVals)
        layout
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount))).heap =
      (((committedStackSizeState
          (skyReducerScalarsLoadedState s oracleVals)
          layout
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))).heap).write
        layout.nodeCountBase (.int (Int.ofNat s.nodeCount))) by
      simp [committedNodeCountState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackNodeCount)]
  rw [show
      (committedStackSizeState
        (skyReducerScalarsLoadedState s oracleVals)
        layout
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))).heap =
      (((committedFocusState
          (skyReducerScalarsLoadedState s oracleVals)
          layout
          (.int (Int.ofNat s.focus))).heap).write
        layout.stackSizeBase (.int (Int.ofNat s.stack.length))) by
      simp [committedStackSizeState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackStackSize)]
  rw [show
      (committedFocusState
        (skyReducerScalarsLoadedState s oracleVals)
        layout
        (.int (Int.ofNat s.focus))).heap =
      ((skyReducerScalarsLoadedState s oracleVals).heap.write
        layout.focusBase (.int (Int.ofNat s.focus))) by
      simp [committedFocusState, layout]]
  rw [readNatArray?_write_other _ _ _ _ _ (Or.inr hStackFocus)]
  simpa [layout, skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
    skyReducerFocusLoadedState, skyReducerEntry, encodeExecStateWithLayout, updateVar_heap,
    enterBlockState_heap] using readStack_encodeHeapWithLayout s oracleVals

theorem decodeKernelState?_committedScalarsLoadedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (committedNodeCountState
        (skyReducerScalarsLoadedState s oracleVals)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount))) = some s := by
  have hTags := readTags_committedScalarsLoadedState s oracleVals hwf
  have hLhs := readLhs_committedScalarsLoadedState s oracleVals hwf
  have hRhs := readRhs_committedScalarsLoadedState s oracleVals hwf
  have hRefs := readOracleRefs_committedScalarsLoadedState s oracleVals hwf
  have hStack := readStack_committedScalarsLoadedState s oracleVals
  rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, _hstack⟩
  rw [decodeKernelState?]
  rw [readFocus_committedScalarsLoadedState]
  rw [readStackSize_committedScalarsLoadedState]
  rw [readNodeCount_committedScalarsLoadedState]
  simp [Option.bind]
  cases hT :
      readIntArray?
        (committedNodeCountState
          (skyReducerScalarsLoadedState s oracleVals)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount))).heap
        (layoutForState s oracleVals).tagsBase s.nodeCount with
  | none =>
      rw [hT] at hTags
      simp at hTags
  | some tags =>
      rw [hT] at hTags
      simp at hTags ⊢
      have hTagsEq : tags = s.tags := by
        simpa using hTags
      subst tags
      cases hL :
          readNatArray?
            (committedNodeCountState
              (skyReducerScalarsLoadedState s oracleVals)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount))).heap
            (layoutForState s oracleVals).lhsBase s.nodeCount with
      | none =>
          rw [hL] at hLhs
          simp at hLhs
      | some lhs =>
          rw [hL] at hLhs
          simp at hLhs ⊢
          have hLhsEq : lhs = s.lhs := by
            simpa using hLhs
          subst lhs
          cases hR :
              readNatArray?
                (committedNodeCountState
                  (skyReducerScalarsLoadedState s oracleVals)
                  (layoutForState s oracleVals)
                  (.int (Int.ofNat s.focus))
                  (.int (Int.ofNat s.stack.length))
                  (.int (Int.ofNat s.nodeCount))).heap
                (layoutForState s oracleVals).rhsBase s.nodeCount with
          | none =>
              rw [hR] at hRhs
              simp at hRhs
          | some rhs =>
              rw [hR] at hRhs
              simp at hRhs ⊢
              have hRhsEq : rhs = s.rhs := by
                simpa using hRhs
              subst rhs
              cases hRef :
                  readNatArray?
                    (committedNodeCountState
                      (skyReducerScalarsLoadedState s oracleVals)
                      (layoutForState s oracleVals)
                      (.int (Int.ofNat s.focus))
                      (.int (Int.ofNat s.stack.length))
                      (.int (Int.ofNat s.nodeCount))).heap
                    (layoutForState s oracleVals).refsBase s.nodeCount with
              | none =>
                  rw [hRef] at hRefs
                  simp at hRefs
              | some refs =>
                  rw [hRef] at hRefs
                  simp at hRefs ⊢
                  have hRefsEq : refs = s.oracleRefs := by
                    simpa using hRefs
                  subst refs
                  cases hS :
                      readNatArray?
                        (committedNodeCountState
                          (skyReducerScalarsLoadedState s oracleVals)
                          (layoutForState s oracleVals)
                          (.int (Int.ofNat s.focus))
                          (.int (Int.ofNat s.stack.length))
                          (.int (Int.ofNat s.nodeCount))).heap
                        (layoutForState s oracleVals).stackBase s.stack.length with
                  | none =>
                      rw [hS] at hStack
                      simp at hStack
                  | some stackCells =>
                      rw [hS] at hStack
                      simp at hStack ⊢
                      have hStackEq : stackCells = s.stack.reverse.toArray := by
                        simpa using hStack
                      subst stackCells
                      simp [hlhs, hrhs, hrefs, hnodes]

theorem decodeKernelState?_committedTagLoadedState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) :
    decodeKernelState? s.maxNodes (layoutForState s oracleVals)
      (committedNodeCountState
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount))) = some s := by
  simpa [skyReducerAppTagLoadedState, updateVar_heap] using
    decodeKernelState?_committedScalarsLoadedState s oracleVals hwf

theorem runLoweredStep?_of_execResult
    (s : State) (oracleVals : Array Int) (status : StepStatus) (out : State) (after : CState)
    (hexec : execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int status.code) after))
    (hdecode : decodeKernelState? s.maxNodes (layoutForState s oracleVals) after = some out) :
    runLoweredStep? s oracleVals = some (status, out) := by
  simp [runLoweredStep?]
  rw [hexec]
  cases status <;> simp [StepStatus.ofCode?, StepStatus.code, hdecode]

theorem runLoweredStep?_invalidFocus
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : ¬ s.focus < s.nodeCount) :
    runLoweredStep? s oracleVals = some (.halted, s) := by
  simp [runLoweredStep?]
  rw [execStmt_invalidFocus_encodeExecState_runLoweredBudget s oracleVals hfocus]
  simp [StepStatus.ofCode?, StepStatus.code]
  have hdecode := decodeKernelState?_committedScalarsLoadedState s oracleVals hwf
  have hbind :
      (decodeKernelState? s.maxNodes (layoutForState s oracleVals)
          (committedNodeCountState
            (skyReducerScalarsLoadedState s oracleVals)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))).bind
        (fun a => some (StepStatus.halted, a)) =
      (some s).bind (fun a => some (StepStatus.halted, a)) := by
    exact congrArg (fun o : Option State => o.bind (fun a => some (StepStatus.halted, a))) hdecode
  simpa [Option.bind] using hbind

theorem runLoweredStep?_focusOutOfRange
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : ¬ s.focus < s.nodeCount) :
    runLoweredStep? s oracleVals = some (.halted, s) := by
  simp [runLoweredStep?]
  rw [execStmt_focusOutOfRange_encodeExecState_runLoweredBudget s oracleVals hfocus]
  simp [StepStatus.ofCode?, StepStatus.code]
  have hDecode :
      decodeKernelState? s.maxNodes (layoutForState s oracleVals)
        (skyReducerScalarsCommittedState s oracleVals) =
          some s := by
    exact decodeKernelState?_skyReducerScalarsCommittedState s oracleVals hwf
  rw [hDecode]
  rfl

def skyReducerTagSwitchStmt : CStmt :=
  switchMany (.var "tag")
    [ (NodeTag.code .app, SKYLowering.appCase)
    , (NodeTag.code .combK, SKYLowering.kCase)
    , (NodeTag.code .combS, SKYLowering.sCase)
    , (NodeTag.code .combY, SKYLowering.yCase)
    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
    (SKYLowering.commitAndReturn .halted)

def skyReducerTagPrefixStmt : CStmt :=
  .seq (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus"))) skyReducerTagSwitchStmt

def skyReducerEntryBodyStmt : CStmt :=
  SKYLowering.seqs
    [ .assign (.var "focus") (.deref (.var "focusPtr"))
    , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
    , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
    , .ite
        (.binop .lt (.var "focus") (.var "nodeCount"))
        skyReducerTagPrefixStmt
        (SKYLowering.commitAndReturn .halted)
    ]

theorem execStmt_tagPrefix_of_tagSwitch
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    {fuel : Nat} {res : ExecResult}
    (hfuel : 0 < fuel)
    (hswitch : execStmt fuel skyReducerTagSwitchStmt
      (skyReducerAppTagLoadedState s oracleVals hfocus) = some res) :
    execStmt (fuel + 1) skyReducerTagPrefixStmt (skyReducerScalarsLoadedState s oracleVals) = some res := by
  have hseq :
      execStmt (fuel + 1)
        (.seq (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus"))) skyReducerTagSwitchStmt)
        (skyReducerScalarsLoadedState s oracleVals) = some res := by
    calc
      execStmt (fuel + 1)
          (.seq (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus"))) skyReducerTagSwitchStmt)
          (skyReducerScalarsLoadedState s oracleVals)
        = execStmt fuel skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            exact execStmt_seq_of_normal fuel
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              skyReducerTagSwitchStmt
              (skyReducerScalarsLoadedState s oracleVals)
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (by
                cases fuel with
                | zero =>
                    cases Nat.not_lt_zero 0 hfuel
                | succ fuel =>
                    simpa [skyReducerTagPrefixStmt, execStmt, skyReducerAppTagLoadedState] using
                      execStmt_loadTag_skyReducerScalarsLoaded s oracleVals hwf hfocus)
      _ = some res := hswitch
  simpa [skyReducerTagPrefixStmt] using hseq

theorem execStmt_validFocusPath_skyReducerEntry_of_tagPrefix
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    {fuel : Nat} {res : ExecResult}
    (hprefix : execStmt fuel skyReducerTagPrefixStmt
      (skyReducerScalarsLoadedState s oracleVals) = some res) :
    execStmt (fuel + 4) skyReducerEntryBodyStmt (skyReducerEntry s oracleVals) = some res := by
  calc
    execStmt (fuel + 4) skyReducerEntryBodyStmt (skyReducerEntry s oracleVals)
      = execStmt (fuel + 3)
          (SKYLowering.seqs
            [ .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
            , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
            , .ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                skyReducerTagPrefixStmt
                (SKYLowering.commitAndReturn .halted)
            ])
          (skyReducerFocusLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal (fuel + 3)
              (.assign (.var "focus") (.deref (.var "focusPtr")))
              (SKYLowering.seqs
                [ .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
                , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
                , .ite
                    (.binop .lt (.var "focus") (.var "nodeCount"))
                    skyReducerTagPrefixStmt
                    (SKYLowering.commitAndReturn .halted)
                ])
              (skyReducerEntry s oracleVals)
              (skyReducerFocusLoadedState s oracleVals)
              (by simpa [execStmt, skyReducerFocusLoadedState] using execStmt_loadFocus_skyReducerEntry s oracleVals)
    _ = execStmt (fuel + 2)
          (SKYLowering.seqs
            [ .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
            , .ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                skyReducerTagPrefixStmt
                (SKYLowering.commitAndReturn .halted)
            ])
          (skyReducerStackSizeLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal (fuel + 2)
              (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
              (SKYLowering.seqs
                [ .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
                , .ite
                    (.binop .lt (.var "focus") (.var "nodeCount"))
                    skyReducerTagPrefixStmt
                    (SKYLowering.commitAndReturn .halted)
                ])
              (skyReducerFocusLoadedState s oracleVals)
              (skyReducerStackSizeLoadedState s oracleVals)
              (by simpa [execStmt, skyReducerStackSizeLoadedState] using
                execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals)
    _ = execStmt (fuel + 1)
          (.ite
            (.binop .lt (.var "focus") (.var "nodeCount"))
            skyReducerTagPrefixStmt
            (SKYLowering.commitAndReturn .halted))
          (skyReducerScalarsLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal (fuel + 1)
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                skyReducerTagPrefixStmt
                (SKYLowering.commitAndReturn .halted))
              (skyReducerStackSizeLoadedState s oracleVals)
              (skyReducerScalarsLoadedState s oracleVals)
              (by simpa [execStmt, skyReducerScalarsLoadedState] using
                execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals)
    _ = execStmt fuel skyReducerTagPrefixStmt (skyReducerScalarsLoadedState s oracleVals) := by
            rw [execStmt_ite_of_eval_true
              (fuel := fuel)
              (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
              (th := skyReducerTagPrefixStmt)
              (el := SKYLowering.commitAndReturn .halted)
              (st := skyReducerScalarsLoadedState s oracleVals)
              (v := .int (if s.focus < s.nodeCount then 1 else 0))]
            · exact skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals
            · simp [hfocus, isTruthy]
    _ = some res := hprefix

theorem skyReducerTagLoadedState_eval_stackThird
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (skyReducerSZVal s hstack) := by
  have hStackLookup :
      (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stack" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase)) := by
    exact skyReducerAppTagLoadedState_lookup_stack s oracleVals hfocus
  have hStackSizeLookup :
      (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "stackSize" =
        some (.int (Int.ofNat s.stack.length)) := by
    exact skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
  have hlen3 : 3 ≤ s.stack.length := hstack
  have hIdxLt : s.stack.length - 3 < s.stack.reverse.length := by
    simp
    omega
  have hThirdIdx : s.stack.length - 1 - (s.stack.length - 3) < s.stack.length := by
    omega
  have hThird :
      s.stack.reverse.get ⟨s.stack.length - 3, hIdxLt⟩ =
        s.stack.get ⟨2, by omega⟩ := by
    have hEq : s.stack.length - 1 - (s.stack.length - 3) = 2 := by
      omega
    simpa [hEq] using
      (List.get_reverse' (l := s.stack) (n := ⟨s.stack.length - 3, hIdxLt⟩) (hn' := hThirdIdx))
  have hSub :
      evalExpr (SKYLowering.stackIx 3) (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.int (Int.ofNat (s.stack.length - 3))) := by
    calc
      evalExpr (SKYLowering.stackIx 3) (skyReducerAppTagLoadedState s oracleVals hfocus)
        = some (.int (Int.ofNat s.stack.length - 3)) := by
            simp [SKYLowering.stackIx, evalExpr, evalStaticExpr, hStackSizeLookup]
      _ = some (.int (Int.ofNat (s.stack.length - 3))) := by
            simp [Int.ofNat_sub hlen3]
  have hAdd :
      evalBinOp .add
        (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackBase))
        (.int (Int.ofNat (s.stack.length - 3))) =
      some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)))) := by
    have hnonneg : 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑(s.stack.length - 3) := by
      omega
    change
      (if 0 ≤ (↑(layoutForState s oracleVals).stackBase : Int) + ↑(s.stack.length - 3) then
        some (CVal.ptr 0
          (Int.ofNat (layoutForState s oracleVals).stackBase + Int.ofNat (s.stack.length - 3)))
      else none) =
        some (CVal.ptr 0 (Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 3))))
    simp [hnonneg]
  have hReadPtr :
      (skyReducerAppTagLoadedState s oracleVals hfocus).readPtr
        { block := 0
          offset := Int.ofNat ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) } =
      (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) := by
    simpa using
      (CState.readPtr_block0
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 3))
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)))
  have hHeapSame :
      (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) =
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) := by
    simp [skyReducerAppTagLoadedState, updateVar_heap]
  have hcell :
      readNatCell? (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals)
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) =
        some (s.stack.get ⟨2, by omega⟩) := by
    let h0 := writeIntList Heap.empty 0 s.tags.toList
    let h1 := writeNatList h0 s.maxNodes s.lhs.toList
    let h2 := writeNatList h1 (s.maxNodes + s.maxNodes) s.rhs.toList
    let h3 := writeNatList h2 (s.maxNodes + s.maxNodes + s.maxNodes) s.oracleRefs.toList
    let h4 := writeIntList h3 (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes)
      (oracleValuesPadded s oracleVals)
    let h5 := writeNatList h4
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals) s.stack.reverse
    let h6 := h5.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1))
      (.int (Int.ofNat s.focus))
    let h7 := h6.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1)
      (.int (Int.ofNat s.stack.length))
    let h8 := h7.write
      (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length + 1) + 1 + 1)
      (.int (Int.ofNat s.nodeCount))
    have hcell' :
        readNatCell? h8
          (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 3)) =
            some (s.stack.get ⟨2, by omega⟩) := by
      simp only [h8, h7, h6]
      have haddrNeNodeCount :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 3) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeNodeCount]
      have haddrNeStackSize :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 3) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) + 1 := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeStackSize]
      have haddrNeFocus :
          s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals + (s.stack.length - 3) ≠
            s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length + 1) := by
        omega
      rw [readNatCell?_write_other _ _ _ _ haddrNeFocus]
      have hAt :
          readNatCell? h5
            (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length - 3)) =
            some (s.stack.reverse.get ⟨s.stack.length - 3, hIdxLt⟩) := by
        simpa [h5, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (readNatCell?_writeNatList_at
            (heap := h4)
            (base := s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals)
            (xs := s.stack.reverse)
            (i := s.stack.length - 3)
            (by simpa using hIdxLt))
      calc
        readNatCell? h5
            (s.maxNodes + s.maxNodes + s.maxNodes + s.maxNodes + oracleSlotCount s oracleVals +
              (s.stack.length - 3))
          = some (s.stack.reverse.get ⟨s.stack.length - 3, hIdxLt⟩) := hAt
        _ = some (s.stack.get ⟨2, by omega⟩) := by
              simpa using congrArg some hThird
    simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, encodeHeapWithLayout, encodeStackWithLayout,
      encodeOracleValuesWithLayout, encodeNodeArraysWithLayout, layoutForState, layoutFor]
      using hcell'
  have hHeap :
      (skyReducerScalarsLoadedState s oracleVals).heap.read
        ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) =
      some (.int (Int.ofNat (s.stack.get ⟨2, by omega⟩))) := by
    have hHeapEnc :
        (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) =
        some (.int (Int.ofNat (s.stack.get ⟨2, by omega⟩))) := by
      cases hread :
          (encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals).read
            ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) with
      | none =>
          simp [readNatCell?, readIntCell?, hread] at hcell
      | some v =>
          cases v with
          | int n =>
              simp [readNatCell?, readIntCell?, hread] at hcell
              have hn : n = Int.ofNat (s.stack.get ⟨2, by omega⟩) := by
                calc
                  n = Int.ofNat n.toNat := by
                    symm
                    exact Int.toNat_of_nonneg hcell.1
                  _ = Int.ofNat (s.stack.get ⟨2, by omega⟩) := by
                    simp [hcell.2]
              simp [hread, hn]
          | ptr block offset =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | uint n sz =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | float v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | null =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | undef =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | structVal fields =>
              simp [readNatCell?, readIntCell?, hread] at hcell
          | unionVal tag v =>
              simp [readNatCell?, readIntCell?, hread] at hcell
    have hHeapEq :
        (skyReducerScalarsLoadedState s oracleVals).heap =
          encodeHeapWithLayout (layoutForState s oracleVals) s oracleVals := by
      simp [skyReducerScalarsLoadedState, skyReducerStackSizeLoadedState,
        skyReducerFocusLoadedState, skyReducerEntry, updateVar_heap,
        HeytingLean.LeanCP.enterBlockState_heap, encodeExecStateWithLayout]
    simpa [hHeapEq] using hHeapEnc
  calc
    evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = (skyReducerAppTagLoadedState s oracleVals hfocus).heap.read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) := by
            simpa [SKYLowering.loadAt, evalExpr, evalStaticExpr, hStackLookup, hSub, hAdd] using hReadPtr
    _ = (skyReducerScalarsLoadedState s oracleVals).heap.read
          ((layoutForState s oracleVals).stackBase + (s.stack.length - 3)) := hHeapSame
    _ = some (skyReducerSZVal s hstack) := by
          simp [skyReducerSZVal, hHeap]

theorem skyReducerSXLoadedState_lookup_x
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXLoadedState s oracleVals hfocus hstack).lookupVar "x" =
      some (skyReducerSXVal s hstack) := by
  rw [skyReducerSXLoadedState]
  exact lookupVar_updateVar_eq (skyReducerAppTagLoadedState s oracleVals hfocus)
    "x" (skyReducerSXVal s hstack)

theorem skyReducerSXLoadedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXLoadedState s oracleVals hfocus hstack).lookupVar "focus" =
      some (.int (Int.ofNat s.focus)) := by
  rw [skyReducerSXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "focus"
      (skyReducerSXVal s hstack) (by decide : "focus" ≠ "x"))

theorem skyReducerSXLoadedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXLoadedState s oracleVals hfocus hstack).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerSXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "stackSize"
      (skyReducerSXVal s hstack) (by decide : "stackSize" ≠ "x"))

theorem skyReducerSXLoadedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXLoadedState s oracleVals hfocus hstack).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerSXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "nodeCount"
      (skyReducerSXVal s hstack) (by decide : "nodeCount" ≠ "x"))

theorem skyReducerSXLoadedState_lookup_tags
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXLoadedState s oracleVals hfocus hstack).lookupVar "tags" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).tagsBase)) := by
  rw [skyReducerSXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "tags"
      (skyReducerSXVal s hstack) (by decide : "tags" ≠ "x"))

theorem skyReducerSXLoadedState_lookup_lhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXLoadedState s oracleVals hfocus hstack).lookupVar "lhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
  rw [skyReducerSXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "lhs"
      (skyReducerSXVal s hstack) (by decide : "lhs" ≠ "x"))

theorem skyReducerSXLoadedState_lookup_rhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXLoadedState s oracleVals hfocus hstack).lookupVar "rhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
  rw [skyReducerSXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "rhs"
      (skyReducerSXVal s hstack) (by decide : "rhs" ≠ "x"))

theorem skyReducerSXLoadedState_lookup_oracleRefs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXLoadedState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
  rw [skyReducerSXLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerAppTagLoadedState s oracleVals hfocus) "x" "oracleRefs"
      (skyReducerSXVal s hstack) (by decide : "oracleRefs" ≠ "x"))

theorem skyReducerSXLoadedState_lookup_maxNodes
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXLoadedState s oracleVals hfocus hstack).lookupVar "maxNodes" =
      some (.int (Int.ofNat s.maxNodes)) := by
  rw [skyReducerSXLoadedState]
  rw [lookupVar_updateVar_ne _ "x" "maxNodes" (skyReducerSXVal s hstack) (by decide)]
  rw [skyReducerAppTagLoadedState]
  rw [lookupVar_updateVar_ne _ "tag" "maxNodes" (.int (s.tags[s.focus]'hfocus)) (by decide)]
  rw [skyReducerScalarsLoadedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "maxNodes" (.int (Int.ofNat s.nodeCount)) (by decide)]
  rw [skyReducerStackSizeLoadedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "maxNodes" (.int (Int.ofNat s.stack.length)) (by decide)]
  rw [skyReducerFocusLoadedState]
  rw [lookupVar_updateVar_ne _ "focus" "maxNodes" (.int (Int.ofNat s.focus)) (by decide)]
  exact skyReducerEntry_lookup_maxNodes s oracleVals

theorem skyReducerSXYLoadedState_lookup_x
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "x" =
      some (skyReducerSXVal s hstack) := by
  rw [skyReducerSXYLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerSXLoadedState s oracleVals hfocus hstack) "y" "x"
      (skyReducerSYVal s hstack) (by decide : "x" ≠ "y"))

theorem skyReducerSXYLoadedState_lookup_y
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "y" =
      some (skyReducerSYVal s hstack) := by
  rw [skyReducerSXYLoadedState]
  exact lookupVar_updateVar_eq (skyReducerSXLoadedState s oracleVals hfocus hstack)
    "y" (skyReducerSYVal s hstack)

theorem skyReducerSXYLoadedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "focus" =
      some (.int (Int.ofNat s.focus)) := by
  rw [skyReducerSXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "focus" (skyReducerSYVal s hstack) (by decide)]
  exact skyReducerSXLoadedState_lookup_focus s oracleVals hfocus hstack

theorem skyReducerSXYLoadedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerSXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "stackSize" (skyReducerSYVal s hstack) (by decide)]
  exact skyReducerSXLoadedState_lookup_stackSize s oracleVals hfocus hstack

theorem skyReducerSXYLoadedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerSXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "nodeCount" (skyReducerSYVal s hstack) (by decide)]
  exact skyReducerSXLoadedState_lookup_nodeCount s oracleVals hfocus hstack

theorem skyReducerSXYLoadedState_lookup_tags
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "tags" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).tagsBase)) := by
  rw [skyReducerSXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "tags" (skyReducerSYVal s hstack) (by decide)]
  exact skyReducerSXLoadedState_lookup_tags s oracleVals hfocus hstack

theorem skyReducerSXYLoadedState_lookup_lhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "lhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
  rw [skyReducerSXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "lhs" (skyReducerSYVal s hstack) (by decide)]
  exact skyReducerSXLoadedState_lookup_lhs s oracleVals hfocus hstack

theorem skyReducerSXYLoadedState_lookup_rhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "rhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
  rw [skyReducerSXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "rhs" (skyReducerSYVal s hstack) (by decide)]
  exact skyReducerSXLoadedState_lookup_rhs s oracleVals hfocus hstack

theorem skyReducerSXYLoadedState_lookup_oracleRefs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
  rw [skyReducerSXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "oracleRefs" (skyReducerSYVal s hstack) (by decide)]
  exact skyReducerSXLoadedState_lookup_oracleRefs s oracleVals hfocus hstack

theorem skyReducerSXYLoadedState_lookup_maxNodes
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYLoadedState s oracleVals hfocus hstack).lookupVar "maxNodes" =
      some (.int (Int.ofNat s.maxNodes)) := by
  rw [skyReducerSXYLoadedState]
  rw [lookupVar_updateVar_ne _ "y" "maxNodes" (skyReducerSYVal s hstack) (by decide)]
  exact skyReducerSXLoadedState_lookup_maxNodes s oracleVals hfocus hstack

theorem skyReducerSXYZLoadedState_lookup_x
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "x" =
      some (skyReducerSXVal s hstack) := by
  rw [skyReducerSXYZLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerSXYLoadedState s oracleVals hfocus hstack) "z" "x"
      (skyReducerSZVal s hstack) (by decide : "x" ≠ "z"))

theorem skyReducerSXYZLoadedState_lookup_y
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "y" =
      some (skyReducerSYVal s hstack) := by
  rw [skyReducerSXYZLoadedState]
  simpa using
    (lookupVar_updateVar_ne (skyReducerSXYLoadedState s oracleVals hfocus hstack) "z" "y"
      (skyReducerSZVal s hstack) (by decide : "y" ≠ "z"))

theorem skyReducerSXYZLoadedState_lookup_z
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "z" =
      some (skyReducerSZVal s hstack) := by
  rw [skyReducerSXYZLoadedState]
  exact lookupVar_updateVar_eq (skyReducerSXYLoadedState s oracleVals hfocus hstack)
    "z" (skyReducerSZVal s hstack)

theorem skyReducerSXYZLoadedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "focus" =
      some (.int (Int.ofNat s.focus)) := by
  rw [skyReducerSXYZLoadedState]
  rw [lookupVar_updateVar_ne _ "z" "focus" (skyReducerSZVal s hstack) (by decide)]
  exact skyReducerSXYLoadedState_lookup_focus s oracleVals hfocus hstack

theorem skyReducerSXYZLoadedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "stackSize" =
      some (.int (Int.ofNat s.stack.length)) := by
  rw [skyReducerSXYZLoadedState]
  rw [lookupVar_updateVar_ne _ "z" "stackSize" (skyReducerSZVal s hstack) (by decide)]
  exact skyReducerSXYLoadedState_lookup_stackSize s oracleVals hfocus hstack

theorem skyReducerSXYZLoadedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "nodeCount" =
      some (.int (Int.ofNat s.nodeCount)) := by
  rw [skyReducerSXYZLoadedState]
  rw [lookupVar_updateVar_ne _ "z" "nodeCount" (skyReducerSZVal s hstack) (by decide)]
  exact skyReducerSXYLoadedState_lookup_nodeCount s oracleVals hfocus hstack

theorem skyReducerSXYZLoadedState_lookup_tags
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "tags" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).tagsBase)) := by
  rw [skyReducerSXYZLoadedState]
  rw [lookupVar_updateVar_ne _ "z" "tags" (skyReducerSZVal s hstack) (by decide)]
  exact skyReducerSXYLoadedState_lookup_tags s oracleVals hfocus hstack

theorem skyReducerSXYZLoadedState_lookup_lhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "lhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
  rw [skyReducerSXYZLoadedState]
  rw [lookupVar_updateVar_ne _ "z" "lhs" (skyReducerSZVal s hstack) (by decide)]
  exact skyReducerSXYLoadedState_lookup_lhs s oracleVals hfocus hstack

theorem skyReducerSXYZLoadedState_lookup_rhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "rhs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
  rw [skyReducerSXYZLoadedState]
  rw [lookupVar_updateVar_ne _ "z" "rhs" (skyReducerSZVal s hstack) (by decide)]
  exact skyReducerSXYLoadedState_lookup_rhs s oracleVals hfocus hstack

theorem skyReducerSXYZLoadedState_lookup_oracleRefs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
  rw [skyReducerSXYZLoadedState]
  rw [lookupVar_updateVar_ne _ "z" "oracleRefs" (skyReducerSZVal s hstack) (by decide)]
  exact skyReducerSXYLoadedState_lookup_oracleRefs s oracleVals hfocus hstack

theorem skyReducerSXYZLoadedState_lookup_maxNodes
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSXYZLoadedState s oracleVals hfocus hstack).lookupVar "maxNodes" =
      some (.int (Int.ofNat s.maxNodes)) := by
  rw [skyReducerSXYZLoadedState]
  rw [lookupVar_updateVar_ne _ "z" "maxNodes" (skyReducerSZVal s hstack) (by decide)]
  exact skyReducerSXYLoadedState_lookup_maxNodes s oracleVals hfocus hstack

theorem execStmt_sLoadX_tagLoaded
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt (fuel + 1)
      (.assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1)))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.normal (skyReducerSXLoadedState s oracleVals hfocus hstack)) := by
  have hstack2 : 2 ≤ s.stack.length := by omega
  have hEval :
      evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
        (skyReducerAppTagLoadedState s oracleVals hfocus) =
          some (skyReducerSXVal s hstack) := by
    simpa [skyReducerKXVal, skyReducerSXVal] using
      (skyReducerTagLoadedState_eval_stackTop s oracleVals hfocus hstack2)
  simp [execStmt, skyReducerSXLoadedState, hEval]

theorem execStmt_sLoadY_afterX
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt (fuel + 1)
      (.assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2)))
      (skyReducerSXLoadedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSXYLoadedState s oracleVals hfocus hstack)) := by
  have hstack2 : 2 ≤ s.stack.length := by omega
  have hEval :
      evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
        (skyReducerSXLoadedState s oracleVals hfocus hstack) =
          some (skyReducerSYVal s hstack) := by
    simpa [skyReducerSXLoadedState, updateVar_heap] using
      (skyReducerTagLoadedState_eval_stackSecond s oracleVals hfocus hstack2)
  simp [execStmt, skyReducerSXYLoadedState, hEval]

set_option maxHeartbeats 2000000 in
theorem execStmt_sLoadZ_afterY
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt (fuel + 1)
      (.assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3)))
      (skyReducerSXYLoadedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSXYZLoadedState s oracleVals hfocus hstack)) := by
  have hEval :
      evalExpr (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
        (skyReducerSXYLoadedState s oracleVals hfocus hstack) =
          some (skyReducerSZVal s hstack) := by
    simpa [skyReducerSXYLoadedState, updateVar_heap] using
      (skyReducerTagLoadedState_eval_stackThird s oracleVals hfocus hstack)
  simp [execStmt, skyReducerSXYZLoadedState, hEval]

theorem execStmt_sStoreNode0Tag_afterLoadZ
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr)
      (skyReducerSXYZLoadedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode0TagStoredState s oracleVals hfocus hstack)) := by
  have hBase := skyReducerSXYZLoadedState_lookup_tags s oracleVals hfocus hstack
  have hNodeCount := skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack
  have hAddr :
      evalExpr (.binop .add (.var "tags") (SKYLowering.nodeIx 0))
        (skyReducerSXYZLoadedState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).tagsBase + s.nodeCount))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSXYZLoadedState s oracleVals hfocus hstack)
        (baseName := "tags") (base := (layoutForState s oracleVals).tagsBase)
        (nodeCount := s.nodeCount) (offset := 0) hBase hNodeCount)
  have hVal :
      evalExpr SKYLowering.appTagExpr (skyReducerSXYZLoadedState s oracleVals hfocus hstack) =
        some (.int (NodeTag.code .app)) := by
    simp [SKYLowering.appTagExpr, evalExpr, evalStaticExpr]
  simpa [skyReducerSNode0TagStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSXYZLoadedState s oracleVals hfocus hstack)
      (base := "tags") (idx := SKYLowering.nodeIx 0) (value := SKYLowering.appTagExpr)
      (addr := (layoutForState s oracleVals).tagsBase + s.nodeCount)
      (v := .int (NodeTag.code .app)) hAddr hVal)

theorem execStmt_sStoreNode0Lhs_afterNode0Tag
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x"))
      (skyReducerSNode0TagStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode0TagStoredState s oracleVals hfocus hstack).lookupVar "lhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
    simpa [skyReducerSNode0TagStoredState] using
      (skyReducerSXYZLoadedState_lookup_lhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode0TagStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode0TagStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "lhs") (SKYLowering.nodeIx 0))
        (skyReducerSNode0TagStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.nodeCount))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode0TagStoredState s oracleVals hfocus hstack)
        (baseName := "lhs") (base := (layoutForState s oracleVals).lhsBase)
        (nodeCount := s.nodeCount) (offset := 0) hBase hNodeCount)
  have hX :
      (skyReducerSNode0TagStoredState s oracleVals hfocus hstack).lookupVar "x" =
        some (skyReducerSXVal s hstack) := by
    simpa [skyReducerSNode0TagStoredState] using
      (skyReducerSXYZLoadedState_lookup_x s oracleVals hfocus hstack)
  have hVal :
      evalExpr (.var "x") (skyReducerSNode0TagStoredState s oracleVals hfocus hstack) =
        some (skyReducerSXVal s hstack) := by
    simp [evalExpr, evalStaticExpr, hX]
  simpa [skyReducerSNode0LhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode0TagStoredState s oracleVals hfocus hstack)
      (base := "lhs") (idx := SKYLowering.nodeIx 0) (value := (.var "x"))
      (addr := (layoutForState s oracleVals).lhsBase + s.nodeCount)
      (v := skyReducerSXVal s hstack) hAddr hVal)

theorem execStmt_sStoreNode0Rhs_afterNode0Lhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z"))
      (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).lookupVar "rhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
    simpa [skyReducerSNode0LhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_rhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode0LhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "rhs") (SKYLowering.nodeIx 0))
        (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).rhsBase + s.nodeCount))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode0LhsStoredState s oracleVals hfocus hstack)
        (baseName := "rhs") (base := (layoutForState s oracleVals).rhsBase)
        (nodeCount := s.nodeCount) (offset := 0) hBase hNodeCount)
  have hZ :
      (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack).lookupVar "z" =
        some (skyReducerSZVal s hstack) := by
    simpa [skyReducerSNode0LhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_z s oracleVals hfocus hstack)
  have hVal :
      evalExpr (.var "z") (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack) =
        some (skyReducerSZVal s hstack) := by
    simp [evalExpr, evalStaticExpr, hZ]
  simpa [skyReducerSNode0RhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode0LhsStoredState s oracleVals hfocus hstack)
      (base := "rhs") (idx := SKYLowering.nodeIx 0) (value := (.var "z"))
      (addr := (layoutForState s oracleVals).rhsBase + s.nodeCount)
      (v := skyReducerSZVal s hstack) hAddr hVal)

theorem execStmt_sStoreNode0Ref_afterNode0Rhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0))
      (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode0RefStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
    simpa [skyReducerSNode0RhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_oracleRefs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode0RhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "oracleRefs") (SKYLowering.nodeIx 0))
        (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).refsBase + s.nodeCount))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode0RhsStoredState s oracleVals hfocus hstack)
        (baseName := "oracleRefs") (base := (layoutForState s oracleVals).refsBase)
        (nodeCount := s.nodeCount) (offset := 0) hBase hNodeCount)
  have hVal :
      evalExpr (.intLit 0) (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack) =
        some (.int 0) := by
    simp [evalExpr, evalStaticExpr]
  simpa [skyReducerSNode0RefStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode0RhsStoredState s oracleVals hfocus hstack)
      (base := "oracleRefs") (idx := SKYLowering.nodeIx 0) (value := (.intLit 0))
      (addr := (layoutForState s oracleVals).refsBase + s.nodeCount)
      (v := .int 0) hAddr hVal)

theorem execStmt_sStoreNode1Tag_afterNode0Ref
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr)
      (skyReducerSNode0RefStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode1TagStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).lookupVar "tags" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).tagsBase)) := by
    simpa [skyReducerSNode0RefStoredState] using
      (skyReducerSXYZLoadedState_lookup_tags s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode0RefStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode0RefStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "tags") (SKYLowering.nodeIx 1))
        (skyReducerSNode0RefStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).tagsBase + s.nodeCount + 1))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode0RefStoredState s oracleVals hfocus hstack)
        (baseName := "tags") (base := (layoutForState s oracleVals).tagsBase)
        (nodeCount := s.nodeCount) (offset := 1) hBase hNodeCount)
  have hVal :
      evalExpr SKYLowering.appTagExpr (skyReducerSNode0RefStoredState s oracleVals hfocus hstack) =
        some (.int (NodeTag.code .app)) := by
    simp [SKYLowering.appTagExpr, evalExpr, evalStaticExpr]
  simpa [skyReducerSNode1TagStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode0RefStoredState s oracleVals hfocus hstack)
      (base := "tags") (idx := SKYLowering.nodeIx 1) (value := SKYLowering.appTagExpr)
      (addr := (layoutForState s oracleVals).tagsBase + s.nodeCount + 1)
      (v := .int (NodeTag.code .app)) hAddr hVal)

theorem execStmt_sStoreNode1Lhs_afterNode1Tag
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y"))
      (skyReducerSNode1TagStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode1TagStoredState s oracleVals hfocus hstack).lookupVar "lhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
    simpa [skyReducerSNode1TagStoredState] using
      (skyReducerSXYZLoadedState_lookup_lhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode1TagStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode1TagStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "lhs") (SKYLowering.nodeIx 1))
        (skyReducerSNode1TagStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.nodeCount + 1))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode1TagStoredState s oracleVals hfocus hstack)
        (baseName := "lhs") (base := (layoutForState s oracleVals).lhsBase)
        (nodeCount := s.nodeCount) (offset := 1) hBase hNodeCount)
  have hY :
      (skyReducerSNode1TagStoredState s oracleVals hfocus hstack).lookupVar "y" =
        some (skyReducerSYVal s hstack) := by
    simpa [skyReducerSNode1TagStoredState] using
      (skyReducerSXYZLoadedState_lookup_y s oracleVals hfocus hstack)
  have hVal :
      evalExpr (.var "y") (skyReducerSNode1TagStoredState s oracleVals hfocus hstack) =
        some (skyReducerSYVal s hstack) := by
    simp [evalExpr, evalStaticExpr, hY]
  simpa [skyReducerSNode1LhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode1TagStoredState s oracleVals hfocus hstack)
      (base := "lhs") (idx := SKYLowering.nodeIx 1) (value := (.var "y"))
      (addr := (layoutForState s oracleVals).lhsBase + s.nodeCount + 1)
      (v := skyReducerSYVal s hstack) hAddr hVal)

theorem execStmt_sStoreNode1Rhs_afterNode1Lhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z"))
      (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).lookupVar "rhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
    simpa [skyReducerSNode1LhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_rhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode1LhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "rhs") (SKYLowering.nodeIx 1))
        (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).rhsBase + s.nodeCount + 1))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode1LhsStoredState s oracleVals hfocus hstack)
        (baseName := "rhs") (base := (layoutForState s oracleVals).rhsBase)
        (nodeCount := s.nodeCount) (offset := 1) hBase hNodeCount)
  have hZ :
      (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack).lookupVar "z" =
        some (skyReducerSZVal s hstack) := by
    simpa [skyReducerSNode1LhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_z s oracleVals hfocus hstack)
  have hVal :
      evalExpr (.var "z") (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack) =
        some (skyReducerSZVal s hstack) := by
    simp [evalExpr, evalStaticExpr, hZ]
  simpa [skyReducerSNode1RhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode1LhsStoredState s oracleVals hfocus hstack)
      (base := "rhs") (idx := SKYLowering.nodeIx 1) (value := (.var "z"))
      (addr := (layoutForState s oracleVals).rhsBase + s.nodeCount + 1)
      (v := skyReducerSZVal s hstack) hAddr hVal)

theorem execStmt_sStoreNode1Ref_afterNode1Rhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0))
      (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode1RefStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
    simpa [skyReducerSNode1RhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_oracleRefs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode1RhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "oracleRefs") (SKYLowering.nodeIx 1))
        (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).refsBase + s.nodeCount + 1))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode1RhsStoredState s oracleVals hfocus hstack)
        (baseName := "oracleRefs") (base := (layoutForState s oracleVals).refsBase)
        (nodeCount := s.nodeCount) (offset := 1) hBase hNodeCount)
  have hVal :
      evalExpr (.intLit 0) (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack) =
        some (.int 0) := by
    simp [evalExpr, evalStaticExpr]
  simpa [skyReducerSNode1RefStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode1RhsStoredState s oracleVals hfocus hstack)
      (base := "oracleRefs") (idx := SKYLowering.nodeIx 1) (value := (.intLit 0))
      (addr := (layoutForState s oracleVals).refsBase + s.nodeCount + 1)
      (v := .int 0) hAddr hVal)

theorem execStmt_sStoreNode2Tag_afterNode1Ref
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr)
      (skyReducerSNode1RefStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode2TagStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).lookupVar "tags" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).tagsBase)) := by
    simpa [skyReducerSNode1RefStoredState] using
      (skyReducerSXYZLoadedState_lookup_tags s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode1RefStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode1RefStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "tags") (SKYLowering.nodeIx 2))
        (skyReducerSNode1RefStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).tagsBase + s.nodeCount + 2))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode1RefStoredState s oracleVals hfocus hstack)
        (baseName := "tags") (base := (layoutForState s oracleVals).tagsBase)
        (nodeCount := s.nodeCount) (offset := 2) hBase hNodeCount)
  have hVal :
      evalExpr SKYLowering.appTagExpr (skyReducerSNode1RefStoredState s oracleVals hfocus hstack) =
        some (.int (NodeTag.code .app)) := by
    simp [SKYLowering.appTagExpr, evalExpr, evalStaticExpr]
  simpa [skyReducerSNode2TagStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode1RefStoredState s oracleVals hfocus hstack)
      (base := "tags") (idx := SKYLowering.nodeIx 2) (value := SKYLowering.appTagExpr)
      (addr := (layoutForState s oracleVals).tagsBase + s.nodeCount + 2)
      (v := .int (NodeTag.code .app)) hAddr hVal)

theorem execStmt_sStoreNode2Lhs_afterNode2Tag
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0))
      (skyReducerSNode2TagStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode2TagStoredState s oracleVals hfocus hstack).lookupVar "lhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).lhsBase)) := by
    simpa [skyReducerSNode2TagStoredState] using
      (skyReducerSXYZLoadedState_lookup_lhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode2TagStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode2TagStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "lhs") (SKYLowering.nodeIx 2))
        (skyReducerSNode2TagStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).lhsBase + s.nodeCount + 2))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode2TagStoredState s oracleVals hfocus hstack)
        (baseName := "lhs") (base := (layoutForState s oracleVals).lhsBase)
        (nodeCount := s.nodeCount) (offset := 2) hBase hNodeCount)
  have hVal :
      evalExpr (SKYLowering.nodeIx 0) (skyReducerSNode2TagStoredState s oracleVals hfocus hstack) =
        some (skyReducerSNode0Val s) := by
    simpa [skyReducerSNode0Val, skyReducerSNode0Nat] using
      (evalExpr_nodeIx_of_lookup (st := skyReducerSNode2TagStoredState s oracleVals hfocus hstack)
        (nodeCount := s.nodeCount) (offset := 0) hNodeCount)
  simpa [skyReducerSNode2LhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode2TagStoredState s oracleVals hfocus hstack)
      (base := "lhs") (idx := SKYLowering.nodeIx 2) (value := SKYLowering.nodeIx 0)
      (addr := (layoutForState s oracleVals).lhsBase + s.nodeCount + 2)
      (v := skyReducerSNode0Val s) hAddr hVal)

theorem execStmt_sStoreNode2Rhs_afterNode2Lhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1))
      (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).lookupVar "rhs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).rhsBase)) := by
    simpa [skyReducerSNode2LhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_rhs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode2LhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "rhs") (SKYLowering.nodeIx 2))
        (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).rhsBase + s.nodeCount + 2))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode2LhsStoredState s oracleVals hfocus hstack)
        (baseName := "rhs") (base := (layoutForState s oracleVals).rhsBase)
        (nodeCount := s.nodeCount) (offset := 2) hBase hNodeCount)
  have hVal :
      evalExpr (SKYLowering.nodeIx 1) (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack) =
        some (skyReducerSNode1Val s) := by
    simpa [skyReducerSNode1Val, skyReducerSNode1Nat] using
      (evalExpr_nodeIx_of_lookup (st := skyReducerSNode2LhsStoredState s oracleVals hfocus hstack)
        (nodeCount := s.nodeCount) (offset := 1) hNodeCount)
  simpa [skyReducerSNode2RhsStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode2LhsStoredState s oracleVals hfocus hstack)
      (base := "rhs") (idx := SKYLowering.nodeIx 2) (value := SKYLowering.nodeIx 1)
      (addr := (layoutForState s oracleVals).rhsBase + s.nodeCount + 2)
      (v := skyReducerSNode1Val s) hAddr hVal)

theorem execStmt_sStoreNode2Ref_afterNode2Rhs
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2
      (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0))
      (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNode2RefStoredState s oracleVals hfocus hstack)) := by
  have hBase :
      (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).lookupVar "oracleRefs" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).refsBase)) := by
    simpa [skyReducerSNode2RhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_oracleRefs s oracleVals hfocus hstack)
  have hNodeCount :
      (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode2RhsStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hAddr :
      evalExpr (.binop .add (.var "oracleRefs") (SKYLowering.nodeIx 2))
        (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack) =
          some (.ptr 0 (Int.ofNat ((layoutForState s oracleVals).refsBase + s.nodeCount + 2))) := by
    simpa [Nat.add_assoc] using
      (evalExpr_basePlusNodeIx_of_lookups
        (st := skyReducerSNode2RhsStoredState s oracleVals hfocus hstack)
        (baseName := "oracleRefs") (base := (layoutForState s oracleVals).refsBase)
        (nodeCount := s.nodeCount) (offset := 2) hBase hNodeCount)
  have hVal :
      evalExpr (.intLit 0) (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack) =
        some (.int 0) := by
    simp [evalExpr, evalStaticExpr]
  simpa [skyReducerSNode2RefStoredState] using
    (execStmt_storeAt_block0_of_evals
      (fuel := 1) (st := skyReducerSNode2RhsStoredState s oracleVals hfocus hstack)
      (base := "oracleRefs") (idx := SKYLowering.nodeIx 2) (value := (.intLit 0))
      (addr := (layoutForState s oracleVals).refsBase + s.nodeCount + 2)
      (v := .int 0) hAddr hVal)

theorem execStmt_sSetFocus_afterStores
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2 (.assign (.var "focus") (SKYLowering.nodeIx 2))
      (skyReducerSNode2RefStoredState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSFocusUpdatedState s oracleVals hfocus hstack)) := by
  have hNodeCount :
      (skyReducerSNode2RefStoredState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    simpa [skyReducerSNode2RefStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hEval :
      evalExpr (SKYLowering.nodeIx 2) (skyReducerSNode2RefStoredState s oracleVals hfocus hstack) =
        some (skyReducerSNode2Val s) := by
    simpa [skyReducerSNode2Val, skyReducerSNode2Nat] using
      (evalExpr_nodeIx_of_lookup (st := skyReducerSNode2RefStoredState s oracleVals hfocus hstack)
        (nodeCount := s.nodeCount) (offset := 2) hNodeCount)
  simp [execStmt, skyReducerSFocusUpdatedState, hEval]

theorem execStmt_sIncNodeCount_afterFocus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2 (.assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3)))
      (skyReducerSFocusUpdatedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSNodeCountUpdatedState s oracleVals hfocus hstack)) := by
  have hNodeCount :
      (skyReducerSFocusUpdatedState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat s.nodeCount)) := by
    rw [skyReducerSFocusUpdatedState]
    rw [lookupVar_updateVar_ne _ "focus" "nodeCount" (skyReducerSNode2Val s) (by decide)]
    simpa [skyReducerSNode2RefStoredState] using
      (skyReducerSXYZLoadedState_lookup_nodeCount s oracleVals hfocus hstack)
  have hEval :
      evalExpr (.binop .add (.var "nodeCount") (.intLit 3))
        (skyReducerSFocusUpdatedState s oracleVals hfocus hstack) =
          some (.int (Int.ofNat (s.nodeCount + 3))) := by
    simp [evalExpr, evalStaticExpr, hNodeCount, Int.ofNat_add]
  simp [execStmt, skyReducerSNodeCountUpdatedState, hEval]

theorem execStmt_sDecStackSize_afterNodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2 (.assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3)))
      (skyReducerSNodeCountUpdatedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack)) := by
  have hStackSize :
      (skyReducerSNodeCountUpdatedState s oracleVals hfocus hstack).lookupVar "stackSize" =
        some (.int (Int.ofNat s.stack.length)) := by
    rw [skyReducerSNodeCountUpdatedState]
    rw [lookupVar_updateVar_ne _ "nodeCount" "stackSize" (.int (Int.ofNat (s.nodeCount + 3))) (by decide)]
    rw [skyReducerSFocusUpdatedState]
    rw [lookupVar_updateVar_ne _ "focus" "stackSize" (skyReducerSNode2Val s) (by decide)]
    exact skyReducerSXYZLoadedState_lookup_stackSize s oracleVals hfocus hstack
  have hEval :
      evalExpr (.binop .sub (.var "stackSize") (.intLit 3))
        (skyReducerSNodeCountUpdatedState s oracleVals hfocus hstack) =
          some (.int (Int.ofNat (s.stack.length - 3))) := by
    simp [evalExpr, evalStaticExpr, hStackSize, Int.ofNat_sub hstack]
  simp [execStmt, skyReducerSStackSizeUpdatedState, hEval]

theorem skyReducerSStackSizeUpdatedState_lookup_focus
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "focus" =
      some (skyReducerSNode2Val s) := by
  rw [skyReducerSStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focus" (.int (Int.ofNat (s.stack.length - 3))) (by decide)]
  rw [skyReducerSNodeCountUpdatedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "focus" (.int (Int.ofNat (s.nodeCount + 3))) (by decide)]
  rw [skyReducerSFocusUpdatedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerSNode2RefStoredState s oracleVals hfocus hstack)
      "focus" (skyReducerSNode2Val s)

theorem skyReducerSStackSizeUpdatedState_lookup_stackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "stackSize" =
      some (.int (Int.ofNat (s.stack.length - 3))) := by
  rw [skyReducerSStackSizeUpdatedState]
  simpa using
    lookupVar_updateVar_eq (skyReducerSNodeCountUpdatedState s oracleVals hfocus hstack)
      "stackSize" (.int (Int.ofNat (s.stack.length - 3)))

set_option maxHeartbeats 2000000 in
theorem skyReducerSStackSizeUpdatedState_lookup_focusPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "focusPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).focusBase)) := by
  rw [skyReducerSStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "focusPtr" (.int (Int.ofNat (s.stack.length - 3))) (by decide)]
  rw [skyReducerSNodeCountUpdatedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "focusPtr" (.int (Int.ofNat (s.nodeCount + 3))) (by decide)]
  rw [skyReducerSFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "focusPtr" (skyReducerSNode2Val s) (by decide)]
  rw [skyReducerSNode2RefStoredState]
  exact skyReducerEntry_lookup_focusPtr s oracleVals

set_option maxHeartbeats 2000000 in
theorem skyReducerSStackSizeUpdatedState_lookup_stackSizePtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "stackSizePtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
  rw [skyReducerSStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "stackSizePtr" (.int (Int.ofNat (s.stack.length - 3))) (by decide)]
  rw [skyReducerSNodeCountUpdatedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "stackSizePtr" (.int (Int.ofNat (s.nodeCount + 3))) (by decide)]
  rw [skyReducerSFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "stackSizePtr" (skyReducerSNode2Val s) (by decide)]
  rw [skyReducerSNode2RefStoredState]
  exact skyReducerEntry_lookup_stackSizePtr s oracleVals

set_option maxHeartbeats 2000000 in
theorem skyReducerSStackSizeUpdatedState_lookup_nodeCountPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "nodeCountPtr" =
      some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
  rw [skyReducerSStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCountPtr" (.int (Int.ofNat (s.stack.length - 3))) (by decide)]
  rw [skyReducerSNodeCountUpdatedState]
  rw [lookupVar_updateVar_ne _ "nodeCount" "nodeCountPtr" (.int (Int.ofNat (s.nodeCount + 3))) (by decide)]
  rw [skyReducerSFocusUpdatedState]
  rw [lookupVar_updateVar_ne _ "focus" "nodeCountPtr" (skyReducerSNode2Val s) (by decide)]
  rw [skyReducerSNode2RefStoredState]
  exact skyReducerEntry_lookup_nodeCountPtr s oracleVals

theorem skyReducerSStackSizeUpdatedState_lookup_nodeCount
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack).lookupVar "nodeCount" =
      some (.int (Int.ofNat (s.nodeCount + 3))) := by
  rw [skyReducerSStackSizeUpdatedState]
  rw [lookupVar_updateVar_ne _ "stackSize" "nodeCount" (.int (Int.ofNat (s.stack.length - 3))) (by decide)]
  exact lookupVar_updateVar_eq (skyReducerSFocusUpdatedState s oracleVals hfocus hstack)
    "nodeCount" (.int (Int.ofNat (s.nodeCount + 3)))

theorem execStmt_sWriteFocusPtr_afterStackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2 (SKYLowering.writeScalar "focusPtr" (.var "focus"))
      (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSCommittedFocusState s oracleVals hfocus hstack)) := by
  simpa [skyReducerSCommittedFocusState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack) "focusPtr" "focus"
      (layoutForState s oracleVals).focusBase (skyReducerSNode2Val s)
      (skyReducerSStackSizeUpdatedState_lookup_focusPtr s oracleVals hfocus hstack)
      (skyReducerSStackSizeUpdatedState_lookup_focus s oracleVals hfocus hstack))

theorem execStmt_sWriteStackSizePtr_afterFocusPtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2 (SKYLowering.writeScalar "stackSizePtr" (.var "stackSize"))
      (skyReducerSCommittedFocusState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack)) := by
  have hPtr :
      (skyReducerSCommittedFocusState s oracleVals hfocus hstack).lookupVar "stackSizePtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).stackSizeBase)) := by
    simpa [skyReducerSCommittedFocusState] using
      (skyReducerSStackSizeUpdatedState_lookup_stackSizePtr s oracleVals hfocus hstack)
  have hVal :
      (skyReducerSCommittedFocusState s oracleVals hfocus hstack).lookupVar "stackSize" =
        some (.int (Int.ofNat (s.stack.length - 3))) := by
    simpa [skyReducerSCommittedFocusState] using
      (skyReducerSStackSizeUpdatedState_lookup_stackSize s oracleVals hfocus hstack)
  simpa [skyReducerSCommittedStackSizeState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerSCommittedFocusState s oracleVals hfocus hstack) "stackSizePtr" "stackSize"
      (layoutForState s oracleVals).stackSizeBase (.int (Int.ofNat (s.stack.length - 3)))
      hPtr hVal)

theorem execStmt_sWriteNodeCountPtr_afterStackSizePtr
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 2 (SKYLowering.writeScalar "nodeCountPtr" (.var "nodeCount"))
      (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack) =
        some (.normal (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
  have hPtr :
      (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).lookupVar "nodeCountPtr" =
        some (.ptr 0 (Int.ofNat (layoutForState s oracleVals).nodeCountBase)) := by
    simpa [skyReducerSCommittedStackSizeState, skyReducerSCommittedFocusState] using
      (skyReducerSStackSizeUpdatedState_lookup_nodeCountPtr s oracleVals hfocus hstack)
  have hVal :
      (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack).lookupVar "nodeCount" =
        some (.int (Int.ofNat (s.nodeCount + 3))) := by
    simpa [skyReducerSCommittedStackSizeState, skyReducerSCommittedFocusState] using
      (skyReducerSStackSizeUpdatedState_lookup_nodeCount s oracleVals hfocus hstack)
  simpa [skyReducerSCommittedState] using
    (execStmt_writeScalar_block0_of_lookups 1
      (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack) "nodeCountPtr" "nodeCount"
      (layoutForState s oracleVals).nodeCountBase (.int (Int.ofNat (s.nodeCount + 3)))
      hPtr hVal)

theorem execStmt_sCommit_afterStackSize
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) :
    execStmt 4 (SKYLowering.commitAndReturn .progress)
      (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
  exact execStmt_commitAndReturn_of_steps .progress
    (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack)
    (skyReducerSCommittedFocusState s oracleVals hfocus hstack)
    (skyReducerSCommittedStackSizeState s oracleVals hfocus hstack)
    (skyReducerSCommittedState s oracleVals hfocus hstack)
    (execStmt_sWriteFocusPtr_afterStackSize s oracleVals hfocus hstack)
    (execStmt_sWriteStackSizePtr_afterFocusPtr s oracleVals hfocus hstack)
    (execStmt_sWriteNodeCountPtr_afterStackSizePtr s oracleVals hfocus hstack)

theorem execStmt_sCase_tagLoaded_progress
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) (hcap : s.nodeCount + 3 ≤ s.maxNodes) :
    execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.progress.code)
        (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
  have hGuardStack :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 3))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 1) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hge : (3 : Int) ≤ s.stack.length := by
      exact_mod_cast hstack
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 3))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 3) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 3 then 1 else 0)) := by rfl
      _ = some (.int 1) := by simp [hge]
  have hGuardCap :
      evalExpr (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 1) := by
    have hNodeCount :
        (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "nodeCount" =
          some (.int (Int.ofNat s.nodeCount)) := by
      rw [skyReducerAppTagLoadedState]
      rw [lookupVar_updateVar_ne _ "tag" "nodeCount" (.int (s.tags[s.focus]'hfocus)) (by decide)]
      exact skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals
    have hMaxNodes :
        (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "maxNodes" =
          some (.int (Int.ofNat s.maxNodes)) := by
      rw [skyReducerAppTagLoadedState]
      rw [lookupVar_updateVar_ne _ "tag" "maxNodes" (.int (s.tags[s.focus]'hfocus)) (by decide)]
      rw [skyReducerScalarsLoadedState]
      rw [lookupVar_updateVar_ne _ "nodeCount" "maxNodes" (.int (Int.ofNat s.nodeCount)) (by decide)]
      rw [skyReducerStackSizeLoadedState]
      rw [lookupVar_updateVar_ne _ "stackSize" "maxNodes" (.int (Int.ofNat s.stack.length)) (by decide)]
      rw [skyReducerFocusLoadedState]
      rw [lookupVar_updateVar_ne _ "focus" "maxNodes" (.int (Int.ofNat s.focus)) (by decide)]
      exact skyReducerEntry_lookup_maxNodes s oracleVals
    have hAdd :
        evalExpr (.binop .add (.var "nodeCount") (.intLit 3))
          (skyReducerAppTagLoadedState s oracleVals hfocus) =
            some (.int (Int.ofNat (s.nodeCount + 3))) := by
      calc
        evalExpr (.binop .add (.var "nodeCount") (.intLit 3))
            (skyReducerAppTagLoadedState s oracleVals hfocus)
          = evalBinOp .add (.int (Int.ofNat s.nodeCount)) (.int 3) := by
              simp [evalExpr, evalStaticExpr, hNodeCount]
        _ = some (.int (Int.ofNat (s.nodeCount + 3))) := by
              simpa [Int.ofNat_add] using
                (rfl :
                  evalBinOp .add (.int (Int.ofNat s.nodeCount)) (.int 3) =
                    some (.int (Int.ofNat s.nodeCount + 3)))
    have hle : (s.nodeCount + 3 : Int) ≤ s.maxNodes := by
      exact_mod_cast hcap
    calc
      evalExpr (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .le (.int (Int.ofNat (s.nodeCount + 3))) (.int (Int.ofNat s.maxNodes)) := by
            simp [evalExpr, evalStaticExpr, hAdd, hMaxNodes]
      _ = some (.int (if Int.ofNat (s.nodeCount + 3) ≤ Int.ofNat s.maxNodes then 1 else 0)) := by
            rfl
      _ = some (.int 1) := by simp [hle]
  calc
    execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 23
          (.ite
            (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
            (SKYLowering.seqs
              [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
              , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
              , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
              , .assign (.var "focus") (SKYLowering.nodeIx 2)
              , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
              , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
              , SKYLowering.commitAndReturn .progress ])
            (SKYLowering.commitAndReturn .outOfHeap))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.sCase, SKYLowering.seqs] using
              (execStmt_ite_of_eval_true
                (fuel := 23)
                (cond := (.binop .ge (.var "stackSize") (.intLit 3)))
                (th := (.ite
                  (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
                  (SKYLowering.seqs
                    [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                    , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                    , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                    , .assign (.var "focus") (SKYLowering.nodeIx 2)
                    , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.commitAndReturn .outOfHeap)))
                (el := SKYLowering.commitAndReturn .halted)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 1)
                hGuardStack
                (by simp [isTruthy]))
    _ = execStmt 22
          (SKYLowering.seqs
            [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
            , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
            , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.seqs] using
              (execStmt_ite_of_eval_true
                (fuel := 22)
                (cond := (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes")))
                (th := SKYLowering.seqs
                  [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                  , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                  , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                  , .assign (.var "focus") (SKYLowering.nodeIx 2)
                  , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                  , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                  , SKYLowering.commitAndReturn .progress ])
                (el := SKYLowering.commitAndReturn .outOfHeap)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 1)
                hGuardCap
                (by simp [isTruthy]))
    _ = execStmt 21
          (SKYLowering.seqs
            [ .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
            , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSXLoadedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 21
              (.assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1)))
              (SKYLowering.seqs
                [ .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (skyReducerSXLoadedState s oracleVals hfocus hstack)
              (execStmt_sLoadX_tagLoaded 21 s oracleVals hfocus hstack)
    _ = execStmt 20
          (SKYLowering.seqs
            [ .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSXYLoadedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 20
              (.assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2)))
              (SKYLowering.seqs
                [ .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSXLoadedState s oracleVals hfocus hstack)
              (skyReducerSXYLoadedState s oracleVals hfocus hstack)
              (execStmt_sLoadY_afterX 20 s oracleVals hfocus hstack)
    _ = execStmt 19
          (SKYLowering.seqs
            [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSXYZLoadedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 19
              (.assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3)))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSXYLoadedState s oracleVals hfocus hstack)
              (skyReducerSXYZLoadedState s oracleVals hfocus hstack)
              (execStmt_sLoadZ_afterY 19 s oracleVals hfocus hstack)
    _ = execStmt 18
          (SKYLowering.seqs
            [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode0TagStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 18
              (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr)
              (SKYLowering.seqs
                [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSXYZLoadedState s oracleVals hfocus hstack)
              (skyReducerSNode0TagStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode0Tag_afterLoadZ s oracleVals hfocus hstack)
    _ = execStmt 17
          (SKYLowering.seqs
            [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 17
              (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x"))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode0TagStoredState s oracleVals hfocus hstack)
              (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode0Lhs_afterNode0Tag s oracleVals hfocus hstack)
    _ = execStmt 16
          (SKYLowering.seqs
            [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 16
              (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z"))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode0LhsStoredState s oracleVals hfocus hstack)
              (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode0Rhs_afterNode0Lhs s oracleVals hfocus hstack)
    _ = execStmt 15
          (SKYLowering.seqs
            [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode0RefStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 15
              (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode0RhsStoredState s oracleVals hfocus hstack)
              (skyReducerSNode0RefStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode0Ref_afterNode0Rhs s oracleVals hfocus hstack)
    _ = execStmt 14
          (SKYLowering.seqs
            [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode1TagStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 14
              (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr)
              (SKYLowering.seqs
                [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode0RefStoredState s oracleVals hfocus hstack)
              (skyReducerSNode1TagStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode1Tag_afterNode0Ref s oracleVals hfocus hstack)
    _ = execStmt 13
          (SKYLowering.seqs
            [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 13
              (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y"))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode1TagStoredState s oracleVals hfocus hstack)
              (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode1Lhs_afterNode1Tag s oracleVals hfocus hstack)
    _ = execStmt 12
          (SKYLowering.seqs
            [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
            , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 12
              (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z"))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode1LhsStoredState s oracleVals hfocus hstack)
              (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode1Rhs_afterNode1Lhs s oracleVals hfocus hstack)
    _ = execStmt 11
          (SKYLowering.seqs
            [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
            , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode1RefStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 11
              (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode1RhsStoredState s oracleVals hfocus hstack)
              (skyReducerSNode1RefStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode1Ref_afterNode1Rhs s oracleVals hfocus hstack)
    _ = execStmt 10
          (SKYLowering.seqs
            [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
            , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode2TagStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 10
              (SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr)
              (SKYLowering.seqs
                [ SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode1RefStoredState s oracleVals hfocus hstack)
              (skyReducerSNode2TagStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode2Tag_afterNode1Ref s oracleVals hfocus hstack)
    _ = execStmt 9
          (SKYLowering.seqs
            [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
            , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 9
              (SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode2TagStoredState s oracleVals hfocus hstack)
              (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode2Lhs_afterNode2Tag s oracleVals hfocus hstack)
    _ = execStmt 8
          (SKYLowering.seqs
            [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
            , .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 8
              (SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1))
              (SKYLowering.seqs
                [ SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                , .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode2LhsStoredState s oracleVals hfocus hstack)
              (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode2Rhs_afterNode2Lhs s oracleVals hfocus hstack)
    _ = execStmt 7
          (SKYLowering.seqs
            [ .assign (.var "focus") (SKYLowering.nodeIx 2)
            , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNode2RefStoredState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 7
              (SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0))
              (SKYLowering.seqs
                [ .assign (.var "focus") (SKYLowering.nodeIx 2)
                , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode2RhsStoredState s oracleVals hfocus hstack)
              (skyReducerSNode2RefStoredState s oracleVals hfocus hstack)
              (execStmt_sStoreNode2Ref_afterNode2Rhs s oracleVals hfocus hstack)
    _ = execStmt 6
          (SKYLowering.seqs
            [ .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSFocusUpdatedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 6
              (.assign (.var "focus") (SKYLowering.nodeIx 2))
              (SKYLowering.seqs
                [ .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSNode2RefStoredState s oracleVals hfocus hstack)
              (skyReducerSFocusUpdatedState s oracleVals hfocus hstack)
              (execStmt_sSetFocus_afterStores s oracleVals hfocus hstack)
    _ = execStmt 5
          (SKYLowering.seqs
            [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
            , SKYLowering.commitAndReturn .progress ])
          (skyReducerSNodeCountUpdatedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 5
              (.assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3)))
              (SKYLowering.seqs
                [ .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                , SKYLowering.commitAndReturn .progress ])
              (skyReducerSFocusUpdatedState s oracleVals hfocus hstack)
              (skyReducerSNodeCountUpdatedState s oracleVals hfocus hstack)
              (execStmt_sIncNodeCount_afterFocus s oracleVals hfocus hstack)
    _ = execStmt 4 (SKYLowering.commitAndReturn .progress)
          (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack) := by
            exact execStmt_seq_of_normal 4
              (.assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3)))
              (SKYLowering.commitAndReturn .progress)
              (skyReducerSNodeCountUpdatedState s oracleVals hfocus hstack)
              (skyReducerSStackSizeUpdatedState s oracleVals hfocus hstack)
              (execStmt_sDecStackSize_afterNodeCount s oracleVals hfocus hstack)
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
            exact execStmt_sCommit_afterStackSize s oracleVals hfocus hstack

theorem execStmt_tagSwitch_s_of_tagLoaded
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 27
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
  simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
    skyReducerAppTagLoadedState, lookupVar_updateVar_eq, hs, NodeTag.code]

theorem execStmt_tagSwitch_s_of_tagLoaded_committed
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) (hcap : s.nodeCount + 3 ≤ s.maxNodes)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 27
      (switchMany (.var "tag")
        [ (NodeTag.code .app, SKYLowering.appCase)
        , (NodeTag.code .combK, SKYLowering.kCase)
        , (NodeTag.code .combS, SKYLowering.sCase)
        , (NodeTag.code .combY, SKYLowering.yCase)
        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
        (SKYLowering.commitAndReturn .halted))
      (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
  calc
    execStmt 28
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted))
        (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
          exact execStmt_tagSwitch_s_of_tagLoaded s oracleVals hfocus hs
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
          exact execStmt_sCase_tagLoaded_progress s oracleVals hfocus hstack hcap

theorem execStmt_sTagPrefix_skyReducerScalarsLoaded_committed
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 28
      (.seq
        (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
        (switchMany (.var "tag")
          [ (NodeTag.code .app, SKYLowering.appCase)
          , (NodeTag.code .combK, SKYLowering.kCase)
          , (NodeTag.code .combS, SKYLowering.sCase)
          , (NodeTag.code .combY, SKYLowering.yCase)
          , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
          (SKYLowering.commitAndReturn .halted)))
      (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
  calc
    execStmt 28
        (.seq
          (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted)))
        (skyReducerScalarsLoadedState s oracleVals)
      = execStmt 27
          (switchMany (.var "tag")
            [ (NodeTag.code .app, SKYLowering.appCase)
            , (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            exact execStmt_seq_of_normal 27
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted))
              (skyReducerScalarsLoadedState s oracleVals)
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (by
                simpa [execStmt, skyReducerAppTagLoadedState] using
                  execStmt_loadTag_skyReducerScalarsLoaded s oracleVals hwf hfocus)
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
          exact execStmt_tagSwitch_s_of_tagLoaded_committed s oracleVals hfocus hstack hcap hs

theorem execStmt_sPath_skyReducerEntry
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 32
      (.seq
        (.assign (.var "focus") (.deref (.var "focusPtr")))
        (.seq
          (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))))
      (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
  calc
    execStmt 32
        (.seq
          (.assign (.var "focus") (.deref (.var "focusPtr")))
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted)))))
        (skyReducerEntry s oracleVals)
      = execStmt 31
          (.seq
            (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
            (.seq
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))))
          (skyReducerFocusLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 31
              (.assign (.var "focus") (.deref (.var "focusPtr")))
              (.seq
                (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
                (.seq
                  (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                  (.ite
                    (.binop .lt (.var "focus") (.var "nodeCount"))
                    (.seq
                      (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                      (switchMany (.var "tag")
                        [ (NodeTag.code .app, SKYLowering.appCase)
                        , (NodeTag.code .combK, SKYLowering.kCase)
                        , (NodeTag.code .combS, SKYLowering.sCase)
                        , (NodeTag.code .combY, SKYLowering.yCase)
                        , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                        (SKYLowering.commitAndReturn .halted)))
                    (SKYLowering.commitAndReturn .halted))))
              (skyReducerEntry s oracleVals)
              (skyReducerFocusLoadedState s oracleVals)
              (by simpa [execStmt, skyReducerFocusLoadedState] using execStmt_loadFocus_skyReducerEntry s oracleVals)
    _ = execStmt 30
          (.seq
            (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
            (.ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerStackSizeLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 30
              (.assign (.var "stackSize") (.deref (.var "stackSizePtr")))
              (.seq
                (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
                (.ite
                  (.binop .lt (.var "focus") (.var "nodeCount"))
                  (.seq
                    (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                    (switchMany (.var "tag")
                      [ (NodeTag.code .app, SKYLowering.appCase)
                      , (NodeTag.code .combK, SKYLowering.kCase)
                      , (NodeTag.code .combS, SKYLowering.sCase)
                      , (NodeTag.code .combY, SKYLowering.yCase)
                      , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                      (SKYLowering.commitAndReturn .halted)))
                  (SKYLowering.commitAndReturn .halted)))
              (skyReducerFocusLoadedState s oracleVals)
              (skyReducerStackSizeLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadStackSize_skyReducerFocusLoaded s oracleVals)
    _ = execStmt 29
          (.ite
            (.binop .lt (.var "focus") (.var "nodeCount"))
            (.seq
              (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
              (switchMany (.var "tag")
                [ (NodeTag.code .app, SKYLowering.appCase)
                , (NodeTag.code .combK, SKYLowering.kCase)
                , (NodeTag.code .combS, SKYLowering.sCase)
                , (NodeTag.code .combY, SKYLowering.yCase)
                , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                (SKYLowering.commitAndReturn .halted)))
            (SKYLowering.commitAndReturn .halted))
          (skyReducerScalarsLoadedState s oracleVals) := by
            exact execStmt_seq_of_normal 29
              (.assign (.var "nodeCount") (.deref (.var "nodeCountPtr")))
              (.ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted))
              (skyReducerStackSizeLoadedState s oracleVals)
              (skyReducerScalarsLoadedState s oracleVals)
              (by simpa [execStmt] using execStmt_loadNodeCount_skyReducerStackSizeLoaded s oracleVals)
    _ = execStmt 28
          (.seq
            (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
            (switchMany (.var "tag")
              [ (NodeTag.code .app, SKYLowering.appCase)
              , (NodeTag.code .combK, SKYLowering.kCase)
              , (NodeTag.code .combS, SKYLowering.sCase)
              , (NodeTag.code .combY, SKYLowering.yCase)
              , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
              (SKYLowering.commitAndReturn .halted)))
          (skyReducerScalarsLoadedState s oracleVals) := by
            rw [execStmt_ite_of_eval_true
              (fuel := 28) (cond := (.binop .lt (.var "focus") (.var "nodeCount")))
              (th := (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted))))
              (el := SKYLowering.commitAndReturn .halted)
              (st := skyReducerScalarsLoadedState s oracleVals)
              (v := .int (if s.focus < s.nodeCount then 1 else 0))]
            · exact skyReducerScalarsLoadedState_eval_focusLtNodeCount s oracleVals
            · simp [hfocus, isTruthy]
    _ = some (.returned (.int StepStatus.progress.code)
          (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
            exact execStmt_sTagPrefix_skyReducerScalarsLoaded_committed s oracleVals hwf hfocus hstack hcap hs

theorem execStmt_sPath_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 33 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerSCommittedState s oracleVals hfocus hstack)
            skyReducerLocals)) := by
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 32
          (SKYLowering.seqs
            [ .assign (.var "focus") (.deref (.var "focusPtr"))
            , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
            , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
            , .ite
                (.binop .lt (.var "focus") (.var "nodeCount"))
                (.seq
                  (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                  (switchMany (.var "tag")
                    [ (NodeTag.code .app, SKYLowering.appCase)
                    , (NodeTag.code .combK, SKYLowering.kCase)
                    , (NodeTag.code .combS, SKYLowering.sCase)
                    , (NodeTag.code .combY, SKYLowering.yCase)
                    , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                    (SKYLowering.commitAndReturn .halted)))
                (SKYLowering.commitAndReturn .halted) ])
          (enterBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            [ ("tag", .int)
            , ("focus", .int)
            , ("stackSize", .int)
            , ("nodeCount", .int)
            , ("x", .int)
            , ("y", .int)
            , ("z", .int)
            , ("ref", .int) ]) =
        some (.returned (.int StepStatus.progress.code)
          (skyReducerSCommittedState s oracleVals hfocus hstack)) := by
    simpa [SKYLowering.seqs, skyReducerEntry, skyReducerLocals] using
      (execStmt_sPath_skyReducerEntry s oracleVals hwf hfocus hstack hcap hs)
  rw [hbody]
  rfl

theorem execStmt_sPath_encodeExecState_fuel
    (extra : Nat) (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt (33 + extra) SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerSCommittedState s oracleVals hfocus hstack)
            skyReducerLocals)) := by
  exact execStmt_fuel_mono
    (h := execStmt_sPath_encodeExecState s oracleVals hwf hfocus hstack hcap hs)

theorem execStmt_sPath_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.progress.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (skyReducerSCommittedState s oracleVals hfocus hstack)
            skyReducerLocals)) := by
  simpa using execStmt_sPath_encodeExecState_fuel 367 s oracleVals hwf hfocus hstack hcap hs

theorem runLoweredStep?_s
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.nodeCount + 3 ≤ s.maxNodes)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    runLoweredStep? s oracleVals =
      some (.progress, skyReducerSNextState s hstack) := by
  simp [runLoweredStep?]
  rw [execStmt_sPath_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack hcap hs]
  simp [StepStatus.ofCode?, StepStatus.code]
  rw [decodeKernelState?_skyReducerSCommittedState s oracleVals hwf hfocus hstack hcap]
  simp [StepStatus.ofCode?, StepStatus.code]

theorem execStmt_tagSwitch_invalidTag_halted
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (happ : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .app)
    (hk : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combK)
    (hs : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combS)
    (hy : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combY)
    (horacle : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .oracle) :
    execStmt 9 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
  have hcommit :
      execStmt 4 (SKYLowering.commitAndReturn .halted)
        (skyReducerAppTagLoadedState s oracleVals hfocus) =
          some (.returned (.int StepStatus.halted.code)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_commitAndReturn_tagLoaded .halted s oracleVals hfocus
  calc
    execStmt 9 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 8
          (switchMany (.var "tag")
            [ (NodeTag.code .combK, SKYLowering.kCase)
            , (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simp [skyReducerTagSwitchStmt, switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
              skyReducerAppTagLoadedState, lookupVar_updateVar_eq, happ]
    _ = execStmt 7
          (switchMany (.var "tag")
            [ (NodeTag.code .combS, SKYLowering.sCase)
            , (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
              skyReducerAppTagLoadedState, lookupVar_updateVar_eq, hk]
    _ = execStmt 6
          (switchMany (.var "tag")
            [ (NodeTag.code .combY, SKYLowering.yCase)
            , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
              skyReducerAppTagLoadedState, lookupVar_updateVar_eq, hs]
    _ = execStmt 5
          (switchMany (.var "tag")
            [ (NodeTag.code .oracle, SKYLowering.oracleCase) ]
            (SKYLowering.commitAndReturn .halted))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
              skyReducerAppTagLoadedState, lookupVar_updateVar_eq, hy]
    _ = execStmt 4 (SKYLowering.commitAndReturn .halted)
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simp [switchMany, execStmt_switch_eq_select, evalExpr, evalStaticExpr,
              skyReducerAppTagLoadedState, lookupVar_updateVar_eq, horacle]
    _ = some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := hcommit

theorem execStmt_invalidTag_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount)
    (happ : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .app)
    (hk : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combK)
    (hs : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combS)
    (hy : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combY)
    (horacle : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .oracle) :
    execStmt 15 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  have hswitch := execStmt_tagSwitch_invalidTag_halted s oracleVals hfocus happ hk hs hy horacle
  have hprefix :
      execStmt 10 skyReducerTagPrefixStmt (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_tagPrefix_of_tagSwitch s oracleVals hwf hfocus (fuel := 9) (hfuel := by decide) hswitch
  have hentry :
      execStmt 14 skyReducerEntryBodyStmt (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_validFocusPath_skyReducerEntry_of_tagPrefix s oracleVals hfocus hprefix
  have hbody :
      execStmt 14
        (SKYLowering.seqs
          [ .assign (.var "focus") (.deref (.var "focusPtr"))
          , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
          , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
          , .ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted) ])
        (enterBlockState
          (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
          [ ("tag", .int)
          , ("focus", .int)
          , ("stackSize", .int)
          , ("nodeCount", .int)
          , ("x", .int)
          , ("y", .int)
          , ("z", .int)
          , ("ref", .int) ]) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
    simpa [skyReducerEntryBodyStmt, skyReducerEntry, skyReducerLocals,
      skyReducerTagPrefixStmt, skyReducerTagSwitchStmt] using hentry
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  rw [hbody]
  rfl

theorem execStmt_invalidTag_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount)
    (happ : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .app)
    (hk : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combK)
    (hs : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combS)
    (hy : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combY)
    (horacle : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .oracle) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  simpa using
    (execStmt_fuel_mono (extra := 385)
      (h := execStmt_invalidTag_encodeExecState s oracleVals hwf hfocus happ hk hs hy horacle))

theorem runLoweredStep?_invalidTag
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount)
    (happ : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .app)
    (hk : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combK)
    (hs : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combS)
    (hy : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .combY)
    (horacle : (s.tags[s.focus]'hfocus) ≠ NodeTag.code .oracle) :
    runLoweredStep? s oracleVals = some (.halted, s) := by
  exact runLoweredStep?_of_execResult s oracleVals .halted s
    (restoreBlockState
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (committedNodeCountState
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount)))
      skyReducerLocals)
    (execStmt_invalidTag_encodeExecState_runLoweredBudget s oracleVals hwf hfocus happ hk hs hy horacle)
    (by
      simpa [decodeKernelState?_restoreBlockState] using
        decodeKernelState?_committedTagLoadedState s oracleVals hwf hfocus)

theorem execStmt_kCase_tagLoaded_halted
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : s.stack.length < 2) :
    execStmt 8 SKYLowering.kCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
  have hGuard :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 2))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 0) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hltInt : (s.stack.length : Int) < 2 := by
      exact_mod_cast hstack
    have hnotge : ¬ ((s.stack.length : Int) ≥ 2) := by
      omega
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 2))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 2) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 2 then 1 else 0)) := by
            rfl
      _ = some (.int 0) := by
            simp [hnotge]
  calc
    execStmt 8 SKYLowering.kCase (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 7 (SKYLowering.commitAndReturn .halted)
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.kCase, SKYLowering.seqs] using
              (execStmt_ite_of_eval_false
                (fuel := 7)
                (cond := (.binop .ge (.var "stackSize") (.intLit 2)))
                (th := SKYLowering.seqs
                  [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                  , .assign (.var "focus") (.var "x")
                  , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                  , SKYLowering.commitAndReturn .progress ])
                (el := SKYLowering.commitAndReturn .halted)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 0)
                hGuard
                (by simp [isTruthy]))
    _ = some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
            simpa using
              (execStmt_fuel_mono (extra := 3)
                (h := execStmt_commitAndReturn_tagLoaded .halted s oracleVals hfocus))

theorem execStmt_kShortStack_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 2)
    (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    execStmt 16 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  have hswitch :
      execStmt 10 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    calc
      execStmt 10 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus)
        = execStmt 8 SKYLowering.kCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [skyReducerTagSwitchStmt] using execStmt_tagSwitch_k_of_tagLoaded s oracleVals hfocus hk
      _ = some (.returned (.int StepStatus.halted.code)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))) := by
            exact execStmt_kCase_tagLoaded_halted s oracleVals hfocus hstack
  have hprefix :
      execStmt 11 skyReducerTagPrefixStmt (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_tagPrefix_of_tagSwitch s oracleVals hwf hfocus (fuel := 10) (hfuel := by decide) hswitch
  have hentry :
      execStmt 15 skyReducerEntryBodyStmt (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_validFocusPath_skyReducerEntry_of_tagPrefix s oracleVals hfocus hprefix
  have hbody :
      execStmt 15
        (SKYLowering.seqs
          [ .assign (.var "focus") (.deref (.var "focusPtr"))
          , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
          , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
          , .ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted) ])
        (enterBlockState
          (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
          [ ("tag", .int)
          , ("focus", .int)
          , ("stackSize", .int)
          , ("nodeCount", .int)
          , ("x", .int)
          , ("y", .int)
          , ("z", .int)
          , ("ref", .int) ]) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
    simpa [skyReducerEntryBodyStmt, skyReducerEntry, skyReducerLocals,
      skyReducerTagPrefixStmt, skyReducerTagSwitchStmt] using hentry
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  rw [hbody]
  rfl

theorem execStmt_kShortStack_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 2)
    (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  simpa using
    (execStmt_fuel_mono (extra := 384)
      (h := execStmt_kShortStack_encodeExecState s oracleVals hwf hfocus hstack hk))

theorem runLoweredStep?_kShortStack
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 2)
    (hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK) :
    runLoweredStep? s oracleVals = some (.halted, s) := by
  exact runLoweredStep?_of_execResult s oracleVals .halted s
    (restoreBlockState
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (committedNodeCountState
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount)))
      skyReducerLocals)
    (execStmt_kShortStack_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack hk)
    (by
      simpa [decodeKernelState?_restoreBlockState] using
        decodeKernelState?_committedTagLoadedState s oracleVals hwf hfocus)

theorem execStmt_oracleCase_tagLoaded_halted
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : s.stack.length < 2) :
    execStmt 11 SKYLowering.oracleCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
  have hGuard :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 2))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 0) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hltInt : (s.stack.length : Int) < 2 := by
      exact_mod_cast hstack
    have hnotge : ¬ ((s.stack.length : Int) ≥ 2) := by
      omega
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 2))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 2) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 2 then 1 else 0)) := by
            rfl
      _ = some (.int 0) := by
            simp [hnotge]
  calc
    execStmt 11 SKYLowering.oracleCase (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 10 (SKYLowering.commitAndReturn .halted)
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.oracleCase, SKYLowering.seqs] using
              (execStmt_ite_of_eval_false
                (fuel := 10)
                (cond := (.binop .ge (.var "stackSize") (.intLit 2)))
                (th := SKYLowering.seqs
                  [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                  , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                  , .assign (.var "ref") (SKYLowering.loadAt "oracleRefs" (.var "focus"))
                  , .ite
                      (.binop .ne (SKYLowering.loadAt "oracleValues" (.var "ref")) (.intLit 0))
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "x")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ])
                      (SKYLowering.seqs
                        [ .assign (.var "focus") (.var "y")
                        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
                        , SKYLowering.commitAndReturn .progress ]) ])
                (el := SKYLowering.commitAndReturn .halted)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 0)
                hGuard
                (by simp [isTruthy]))
    _ = some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
            simpa using
              (execStmt_fuel_mono (extra := 6)
                (h := execStmt_commitAndReturn_tagLoaded .halted s oracleVals hfocus))

theorem execStmt_oracleShortStack_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 2)
    (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    execStmt 22 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  have hswitch :
      execStmt 16 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    calc
      execStmt 16 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus)
        = execStmt 11 SKYLowering.oracleCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [skyReducerTagSwitchStmt] using
              execStmt_tagSwitch_oracle_of_tagLoaded s oracleVals hfocus horacleTag
      _ = some (.returned (.int StepStatus.halted.code)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))) := by
            exact execStmt_oracleCase_tagLoaded_halted s oracleVals hfocus hstack
  have hprefix :
      execStmt 17 skyReducerTagPrefixStmt (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_tagPrefix_of_tagSwitch s oracleVals hwf hfocus (fuel := 16) (hfuel := by decide) hswitch
  have hentry :
      execStmt 21 skyReducerEntryBodyStmt (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_validFocusPath_skyReducerEntry_of_tagPrefix s oracleVals hfocus hprefix
  have hbody :
      execStmt 21
        (SKYLowering.seqs
          [ .assign (.var "focus") (.deref (.var "focusPtr"))
          , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
          , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
          , .ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted) ])
        (enterBlockState
          (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
          [ ("tag", .int)
          , ("focus", .int)
          , ("stackSize", .int)
          , ("nodeCount", .int)
          , ("x", .int)
          , ("y", .int)
          , ("z", .int)
          , ("ref", .int) ]) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
    simpa [skyReducerEntryBodyStmt, skyReducerEntry, skyReducerLocals,
      skyReducerTagPrefixStmt, skyReducerTagSwitchStmt] using hentry
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  rw [hbody]
  rfl

theorem execStmt_oracleShortStack_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 2)
    (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  simpa using
    (execStmt_fuel_mono (extra := 378)
      (h := execStmt_oracleShortStack_encodeExecState s oracleVals hwf hfocus hstack horacleTag))

theorem runLoweredStep?_oracleShortStack
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 2)
    (horacleTag : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle) :
    runLoweredStep? s oracleVals = some (.halted, s) := by
  exact runLoweredStep?_of_execResult s oracleVals .halted s
    (restoreBlockState
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (committedNodeCountState
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount)))
      skyReducerLocals)
    (execStmt_oracleShortStack_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack horacleTag)
    (by
      simpa [decodeKernelState?_restoreBlockState] using
        decodeKernelState?_committedTagLoadedState s oracleVals hwf hfocus)

theorem execStmt_yCase_tagLoaded_halted
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : s.stack.length < 1) :
    execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
  have hGuard :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 1))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 0) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hltInt : (s.stack.length : Int) < 1 := by
      exact_mod_cast hstack
    have hnotge : ¬ ((s.stack.length : Int) ≥ 1) := by
      omega
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 1))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 1) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 1 then 1 else 0)) := by
            rfl
      _ = some (.int 0) := by
            simp [hnotge]
  calc
    execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 17 (SKYLowering.commitAndReturn .halted)
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.yCase, SKYLowering.seqs] using
              (execStmt_ite_of_eval_false
                (fuel := 17)
                (cond := (.binop .ge (.var "stackSize") (.intLit 1)))
                (th := (.ite
                  (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
                  (SKYLowering.seqs
                    [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                    , .assign (.var "focus") (SKYLowering.nodeIx 1)
                    , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.commitAndReturn .outOfHeap)))
                (el := SKYLowering.commitAndReturn .halted)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 0)
                hGuard
                (by simp [isTruthy]))
    _ = some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
            simpa using
              (execStmt_fuel_mono (extra := 13)
                (h := execStmt_commitAndReturn_tagLoaded .halted s oracleVals hfocus))

theorem execStmt_yCase_tagLoaded_outOfHeap
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 1 ≤ s.stack.length) (hcap : s.maxNodes < s.nodeCount + 2) :
    execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.outOfHeap.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
  have hGuardStack :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 1))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 1) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hge : (1 : Int) ≤ s.stack.length := by
      exact_mod_cast hstack
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 1))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 1) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 1 then 1 else 0)) := by
            rfl
      _ = some (.int 1) := by
            simp [hge]
  have hGuardCap :
      evalExpr (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 0) := by
    have hNodeCount :
        (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "nodeCount" =
          some (.int (Int.ofNat s.nodeCount)) := by
      rw [skyReducerAppTagLoadedState]
      rw [lookupVar_updateVar_ne _ "tag" "nodeCount" (.int (s.tags[s.focus]'hfocus)) (by decide)]
      exact skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals
    have hMaxNodes :
        (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "maxNodes" =
          some (.int (Int.ofNat s.maxNodes)) := by
      rw [skyReducerAppTagLoadedState]
      rw [lookupVar_updateVar_ne _ "tag" "maxNodes" (.int (s.tags[s.focus]'hfocus)) (by decide)]
      rw [skyReducerScalarsLoadedState]
      rw [lookupVar_updateVar_ne _ "nodeCount" "maxNodes" (.int (Int.ofNat s.nodeCount)) (by decide)]
      rw [skyReducerStackSizeLoadedState]
      rw [lookupVar_updateVar_ne _ "stackSize" "maxNodes" (.int (Int.ofNat s.stack.length)) (by decide)]
      rw [skyReducerFocusLoadedState]
      rw [lookupVar_updateVar_ne _ "focus" "maxNodes" (.int (Int.ofNat s.focus)) (by decide)]
      exact skyReducerEntry_lookup_maxNodes s oracleVals
    have hAdd :
        evalExpr (.binop .add (.var "nodeCount") (.intLit 2))
          (skyReducerAppTagLoadedState s oracleVals hfocus) =
            some (.int (Int.ofNat (s.nodeCount + 2))) := by
      calc
        evalExpr (.binop .add (.var "nodeCount") (.intLit 2))
            (skyReducerAppTagLoadedState s oracleVals hfocus)
          = evalBinOp .add (.int (Int.ofNat s.nodeCount)) (.int 2) := by
              simp [evalExpr, evalStaticExpr, hNodeCount]
        _ = some (.int (Int.ofNat (s.nodeCount + 2))) := by
              simpa [Int.ofNat_add] using
                (rfl :
                  evalBinOp .add (.int (Int.ofNat s.nodeCount)) (.int 2) =
                    some (.int (Int.ofNat s.nodeCount + 2)))
    have hlt : (s.maxNodes : Int) < s.nodeCount + 2 := by
      exact_mod_cast hcap
    have hnotle : ¬ ((s.nodeCount + 2 : Int) ≤ s.maxNodes) := by
      omega
    calc
      evalExpr (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .le (.int (Int.ofNat (s.nodeCount + 2))) (.int (Int.ofNat s.maxNodes)) := by
            simp [evalExpr, evalStaticExpr, hAdd, hMaxNodes]
      _ = some (.int (if Int.ofNat (s.nodeCount + 2) ≤ Int.ofNat s.maxNodes then 1 else 0)) := by
            rfl
      _ = some (.int 0) := by
            simp [hnotle]
  calc
    execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 17
          (.ite
            (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
            (SKYLowering.seqs
              [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
              , .assign (.var "focus") (SKYLowering.nodeIx 1)
              , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
              , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
              , SKYLowering.commitAndReturn .progress ])
            (SKYLowering.commitAndReturn .outOfHeap))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.yCase, SKYLowering.seqs] using
              (execStmt_ite_of_eval_true
                (fuel := 17)
                (cond := (.binop .ge (.var "stackSize") (.intLit 1)))
                (th := (.ite
                  (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
                  (SKYLowering.seqs
                    [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                    , .assign (.var "focus") (SKYLowering.nodeIx 1)
                    , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.commitAndReturn .outOfHeap)))
                (el := SKYLowering.commitAndReturn .halted)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 1)
                hGuardStack
                (by simp [isTruthy]))
    _ = execStmt 16 (SKYLowering.commitAndReturn .outOfHeap)
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.seqs] using
              (execStmt_ite_of_eval_false
                (fuel := 16)
                (cond := (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes")))
                (th := SKYLowering.seqs
                  [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "focus")
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "x")
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "x")
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (SKYLowering.nodeIx 0)
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                  , .assign (.var "focus") (SKYLowering.nodeIx 1)
                  , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
                  , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
                  , SKYLowering.commitAndReturn .progress ])
                (el := SKYLowering.commitAndReturn .outOfHeap)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 0)
                hGuardCap
                (by simp [isTruthy]))
    _ = some (.returned (.int StepStatus.outOfHeap.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
            simpa using
              (execStmt_fuel_mono (extra := 12)
                (h := execStmt_commitAndReturn_tagLoaded .outOfHeap s oracleVals hfocus))

theorem execStmt_yShortStack_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 1)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 28 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  have hswitch :
      execStmt 22 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    calc
      execStmt 22 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus)
        = execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [skyReducerTagSwitchStmt] using
              execStmt_tagSwitch_y_of_tagLoaded s oracleVals hfocus hy
      _ = some (.returned (.int StepStatus.halted.code)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))) := by
            exact execStmt_yCase_tagLoaded_halted s oracleVals hfocus hstack
  have hprefix :
      execStmt 23 skyReducerTagPrefixStmt (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_tagPrefix_of_tagSwitch s oracleVals hwf hfocus (fuel := 22) (hfuel := by decide) hswitch
  have hentry :
      execStmt 27 skyReducerEntryBodyStmt (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_validFocusPath_skyReducerEntry_of_tagPrefix s oracleVals hfocus hprefix
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 27
        (SKYLowering.seqs
          [ .assign (.var "focus") (.deref (.var "focusPtr"))
          , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
          , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
          , .ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted) ])
        (enterBlockState
          (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
          [ ("tag", .int)
          , ("focus", .int)
          , ("stackSize", .int)
          , ("nodeCount", .int)
          , ("x", .int)
          , ("y", .int)
          , ("z", .int)
          , ("ref", .int) ]) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
    simpa [skyReducerEntryBodyStmt, skyReducerEntry, skyReducerLocals,
      skyReducerTagPrefixStmt, skyReducerTagSwitchStmt] using hentry
  rw [hbody]
  rfl

theorem execStmt_yShortStack_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 1)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  simpa using
    (execStmt_fuel_mono (extra := 372)
      (h := execStmt_yShortStack_encodeExecState s oracleVals hwf hfocus hstack hy))

theorem runLoweredStep?_yShortStack
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 1)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    runLoweredStep? s oracleVals = some (.halted, s) := by
  exact runLoweredStep?_of_execResult s oracleVals .halted s
    (restoreBlockState
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (committedNodeCountState
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount)))
      skyReducerLocals)
    (execStmt_yShortStack_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack hy)
    (by
      simpa [decodeKernelState?_restoreBlockState] using
        decodeKernelState?_committedTagLoadedState s oracleVals hwf hfocus)

theorem execStmt_yOutOfHeap_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.maxNodes < s.nodeCount + 2)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 28 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  have hswitch :
      execStmt 22 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    calc
      execStmt 22 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus)
        = execStmt 18 SKYLowering.yCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [skyReducerTagSwitchStmt] using
              execStmt_tagSwitch_y_of_tagLoaded s oracleVals hfocus hy
      _ = some (.returned (.int StepStatus.outOfHeap.code)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))) := by
            exact execStmt_yCase_tagLoaded_outOfHeap s oracleVals hfocus hstack hcap
  have hprefix :
      execStmt 23 skyReducerTagPrefixStmt (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_tagPrefix_of_tagSwitch s oracleVals hwf hfocus (fuel := 22) (hfuel := by decide) hswitch
  have hentry :
      execStmt 27 skyReducerEntryBodyStmt (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_validFocusPath_skyReducerEntry_of_tagPrefix s oracleVals hfocus hprefix
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 27
        (SKYLowering.seqs
          [ .assign (.var "focus") (.deref (.var "focusPtr"))
          , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
          , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
          , .ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted) ])
        (enterBlockState
          (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
          [ ("tag", .int)
          , ("focus", .int)
          , ("stackSize", .int)
          , ("nodeCount", .int)
          , ("x", .int)
          , ("y", .int)
          , ("z", .int)
          , ("ref", .int) ]) =
      some (.returned (.int StepStatus.outOfHeap.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
    simpa [skyReducerEntryBodyStmt, skyReducerEntry, skyReducerLocals,
      skyReducerTagPrefixStmt, skyReducerTagSwitchStmt] using hentry
  rw [hbody]
  rfl

theorem execStmt_yOutOfHeap_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.maxNodes < s.nodeCount + 2)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  simpa using
    (execStmt_fuel_mono (extra := 372)
      (h := execStmt_yOutOfHeap_encodeExecState s oracleVals hwf hfocus hstack hcap hy))

theorem runLoweredStep?_yOutOfHeap
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 1 ≤ s.stack.length)
    (hcap : s.maxNodes < s.nodeCount + 2)
    (hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY) :
    runLoweredStep? s oracleVals = some (.outOfHeap, s) := by
  exact runLoweredStep?_of_execResult s oracleVals .outOfHeap s
    (restoreBlockState
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (committedNodeCountState
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount)))
      skyReducerLocals)
    (execStmt_yOutOfHeap_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack hcap hy)
    (by
      simpa [decodeKernelState?_restoreBlockState] using
        decodeKernelState?_committedTagLoadedState s oracleVals hwf hfocus)

theorem execStmt_sCase_tagLoaded_halted
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : s.stack.length < 3) :
    execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
  have hGuard :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 3))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 0) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hltInt : (s.stack.length : Int) < 3 := by
      exact_mod_cast hstack
    have hnotge : ¬ ((s.stack.length : Int) ≥ 3) := by
      omega
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 3))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 3) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 3 then 1 else 0)) := by
            rfl
      _ = some (.int 0) := by
            simp [hnotge]
  calc
    execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 23 (SKYLowering.commitAndReturn .halted)
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.sCase, SKYLowering.seqs] using
              (execStmt_ite_of_eval_false
                (fuel := 23)
                (cond := (.binop .ge (.var "stackSize") (.intLit 3)))
                (th := (.ite
                  (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
                  (SKYLowering.seqs
                    [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                    , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                    , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                    , .assign (.var "focus") (SKYLowering.nodeIx 2)
                    , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.commitAndReturn .outOfHeap)))
                (el := SKYLowering.commitAndReturn .halted)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 0)
                hGuard
                (by simp [isTruthy]))
    _ = some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
            simpa using
              (execStmt_fuel_mono (extra := 19)
                (h := execStmt_commitAndReturn_tagLoaded .halted s oracleVals hfocus))

theorem execStmt_sCase_tagLoaded_outOfHeap
    (s : State) (oracleVals : Array Int) (hfocus : s.focus < s.nodeCount)
    (hstack : 3 ≤ s.stack.length) (hcap : s.maxNodes < s.nodeCount + 3) :
    execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus) =
      some (.returned (.int StepStatus.outOfHeap.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
  have hGuardStack :
      evalExpr (.binop .ge (.var "stackSize") (.intLit 3))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 1) := by
    have hStackSize := skyReducerAppTagLoadedState_lookup_stackSize s oracleVals hfocus
    have hge : (3 : Int) ≤ s.stack.length := by
      exact_mod_cast hstack
    calc
      evalExpr (.binop .ge (.var "stackSize") (.intLit 3))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .ge (.int (Int.ofNat s.stack.length)) (.int 3) := by
            simp [evalExpr, evalStaticExpr, hStackSize]
      _ = some (.int (if Int.ofNat s.stack.length ≥ 3 then 1 else 0)) := by
            rfl
      _ = some (.int 1) := by
            simp [hge]
  have hGuardCap :
      evalExpr (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
        (skyReducerAppTagLoadedState s oracleVals hfocus) = some (.int 0) := by
    have hNodeCount :
        (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "nodeCount" =
          some (.int (Int.ofNat s.nodeCount)) := by
      rw [skyReducerAppTagLoadedState]
      rw [lookupVar_updateVar_ne _ "tag" "nodeCount" (.int (s.tags[s.focus]'hfocus)) (by decide)]
      exact skyReducerScalarsLoadedState_lookup_nodeCount s oracleVals
    have hMaxNodes :
        (skyReducerAppTagLoadedState s oracleVals hfocus).lookupVar "maxNodes" =
          some (.int (Int.ofNat s.maxNodes)) := by
      rw [skyReducerAppTagLoadedState]
      rw [lookupVar_updateVar_ne _ "tag" "maxNodes" (.int (s.tags[s.focus]'hfocus)) (by decide)]
      rw [skyReducerScalarsLoadedState]
      rw [lookupVar_updateVar_ne _ "nodeCount" "maxNodes" (.int (Int.ofNat s.nodeCount)) (by decide)]
      rw [skyReducerStackSizeLoadedState]
      rw [lookupVar_updateVar_ne _ "stackSize" "maxNodes" (.int (Int.ofNat s.stack.length)) (by decide)]
      rw [skyReducerFocusLoadedState]
      rw [lookupVar_updateVar_ne _ "focus" "maxNodes" (.int (Int.ofNat s.focus)) (by decide)]
      exact skyReducerEntry_lookup_maxNodes s oracleVals
    have hAdd :
        evalExpr (.binop .add (.var "nodeCount") (.intLit 3))
          (skyReducerAppTagLoadedState s oracleVals hfocus) =
            some (.int (Int.ofNat (s.nodeCount + 3))) := by
      calc
        evalExpr (.binop .add (.var "nodeCount") (.intLit 3))
            (skyReducerAppTagLoadedState s oracleVals hfocus)
          = evalBinOp .add (.int (Int.ofNat s.nodeCount)) (.int 3) := by
              simp [evalExpr, evalStaticExpr, hNodeCount]
        _ = some (.int (Int.ofNat (s.nodeCount + 3))) := by
              simpa [Int.ofNat_add] using
                (rfl :
                  evalBinOp .add (.int (Int.ofNat s.nodeCount)) (.int 3) =
                    some (.int (Int.ofNat s.nodeCount + 3)))
    have hlt : (s.maxNodes : Int) < s.nodeCount + 3 := by
      exact_mod_cast hcap
    have hnotle : ¬ ((s.nodeCount + 3 : Int) ≤ s.maxNodes) := by
      omega
    calc
      evalExpr (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
          (skyReducerAppTagLoadedState s oracleVals hfocus)
        = evalBinOp .le (.int (Int.ofNat (s.nodeCount + 3))) (.int (Int.ofNat s.maxNodes)) := by
            simp [evalExpr, evalStaticExpr, hAdd, hMaxNodes]
      _ = some (.int (if Int.ofNat (s.nodeCount + 3) ≤ Int.ofNat s.maxNodes then 1 else 0)) := by
            rfl
      _ = some (.int 0) := by
            simp [hnotle]
  calc
    execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus)
      = execStmt 23
          (.ite
            (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
            (SKYLowering.seqs
              [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
              , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
              , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
              , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
              , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
              , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
              , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
              , .assign (.var "focus") (SKYLowering.nodeIx 2)
              , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
              , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
              , SKYLowering.commitAndReturn .progress ])
            (SKYLowering.commitAndReturn .outOfHeap))
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.sCase, SKYLowering.seqs] using
              (execStmt_ite_of_eval_true
                (fuel := 23)
                (cond := (.binop .ge (.var "stackSize") (.intLit 3)))
                (th := (.ite
                  (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
                  (SKYLowering.seqs
                    [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                    , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                    , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                    , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                    , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                    , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                    , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                    , .assign (.var "focus") (SKYLowering.nodeIx 2)
                    , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                    , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                    , SKYLowering.commitAndReturn .progress ])
                  (SKYLowering.commitAndReturn .outOfHeap)))
                (el := SKYLowering.commitAndReturn .halted)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 1)
                hGuardStack
                (by simp [isTruthy]))
    _ = execStmt 22 (SKYLowering.commitAndReturn .outOfHeap)
          (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [SKYLowering.seqs] using
              (execStmt_ite_of_eval_false
                (fuel := 22)
                (cond := (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes")))
                (th := SKYLowering.seqs
                  [ .assign (.var "x") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 1))
                  , .assign (.var "y") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 2))
                  , .assign (.var "z") (SKYLowering.loadAt "stack" (SKYLowering.stackIx 3))
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 0) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 0) (.var "x")
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 0) (.var "z")
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 0) (.intLit 0)
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 1) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 1) (.var "y")
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 1) (.var "z")
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 1) (.intLit 0)
                  , SKYLowering.storeAt "tags" (SKYLowering.nodeIx 2) SKYLowering.appTagExpr
                  , SKYLowering.storeAt "lhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 0)
                  , SKYLowering.storeAt "rhs" (SKYLowering.nodeIx 2) (SKYLowering.nodeIx 1)
                  , SKYLowering.storeAt "oracleRefs" (SKYLowering.nodeIx 2) (.intLit 0)
                  , .assign (.var "focus") (SKYLowering.nodeIx 2)
                  , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
                  , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
                  , SKYLowering.commitAndReturn .progress ])
                (el := SKYLowering.commitAndReturn .outOfHeap)
                (st := skyReducerAppTagLoadedState s oracleVals hfocus)
                (v := .int 0)
                hGuardCap
                (by simp [isTruthy]))
    _ = some (.returned (.int StepStatus.outOfHeap.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
            simpa using
              (execStmt_fuel_mono (extra := 18)
                (h := execStmt_commitAndReturn_tagLoaded .outOfHeap s oracleVals hfocus))

theorem execStmt_sShortStack_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 3)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 33 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  have hswitch :
      execStmt 27 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    calc
      execStmt 27 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus)
        = execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [skyReducerTagSwitchStmt] using
              execStmt_tagSwitch_s_of_tagLoaded s oracleVals hfocus hs
      _ = some (.returned (.int StepStatus.halted.code)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))) := by
            exact execStmt_sCase_tagLoaded_halted s oracleVals hfocus hstack
  have hprefix :
      execStmt 28 skyReducerTagPrefixStmt (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_tagPrefix_of_tagSwitch s oracleVals hwf hfocus (fuel := 27) (hfuel := by decide) hswitch
  have hentry :
      execStmt 32 skyReducerEntryBodyStmt (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_validFocusPath_skyReducerEntry_of_tagPrefix s oracleVals hfocus hprefix
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 32
        (SKYLowering.seqs
          [ .assign (.var "focus") (.deref (.var "focusPtr"))
          , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
          , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
          , .ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted) ])
        (enterBlockState
          (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
          [ ("tag", .int)
          , ("focus", .int)
          , ("stackSize", .int)
          , ("nodeCount", .int)
          , ("x", .int)
          , ("y", .int)
          , ("z", .int)
          , ("ref", .int) ]) =
      some (.returned (.int StepStatus.halted.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
    simpa [skyReducerEntryBodyStmt, skyReducerEntry, skyReducerLocals,
      skyReducerTagPrefixStmt, skyReducerTagSwitchStmt] using hentry
  rw [hbody]
  rfl

theorem execStmt_sShortStack_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 3)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.halted.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  simpa using
    (execStmt_fuel_mono (extra := 367)
      (h := execStmt_sShortStack_encodeExecState s oracleVals hwf hfocus hstack hs))

theorem runLoweredStep?_sShortStack
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : s.stack.length < 3)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    runLoweredStep? s oracleVals = some (.halted, s) := by
  exact runLoweredStep?_of_execResult s oracleVals .halted s
    (restoreBlockState
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (committedNodeCountState
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount)))
      skyReducerLocals)
    (execStmt_sShortStack_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack hs)
    (by
      simpa [decodeKernelState?_restoreBlockState] using
        decodeKernelState?_committedTagLoadedState s oracleVals hwf hfocus)

theorem execStmt_sOutOfHeap_encodeExecState
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.maxNodes < s.nodeCount + 3)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 33 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  have hswitch :
      execStmt 27 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    calc
      execStmt 27 skyReducerTagSwitchStmt (skyReducerAppTagLoadedState s oracleVals hfocus)
        = execStmt 24 SKYLowering.sCase (skyReducerAppTagLoadedState s oracleVals hfocus) := by
            simpa [skyReducerTagSwitchStmt] using
              execStmt_tagSwitch_s_of_tagLoaded s oracleVals hfocus hs
      _ = some (.returned (.int StepStatus.outOfHeap.code)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))) := by
            exact execStmt_sCase_tagLoaded_outOfHeap s oracleVals hfocus hstack hcap
  have hprefix :
      execStmt 28 skyReducerTagPrefixStmt (skyReducerScalarsLoadedState s oracleVals) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_tagPrefix_of_tagSwitch s oracleVals hwf hfocus (fuel := 27) (hfuel := by decide) hswitch
  have hentry :
      execStmt 32 skyReducerEntryBodyStmt (skyReducerEntry s oracleVals) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (committedNodeCountState
            (skyReducerAppTagLoadedState s oracleVals hfocus)
            (layoutForState s oracleVals)
            (.int (Int.ofNat s.focus))
            (.int (Int.ofNat s.stack.length))
            (.int (Int.ofNat s.nodeCount)))) := by
    exact execStmt_validFocusPath_skyReducerEntry_of_tagPrefix s oracleVals hfocus hprefix
  simp [SKYLowering.skyReducerStepDecl, SKYLowering.skyReducerStepBody, execStmt]
  have hbody :
      execStmt 32
        (SKYLowering.seqs
          [ .assign (.var "focus") (.deref (.var "focusPtr"))
          , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
          , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
          , .ite
              (.binop .lt (.var "focus") (.var "nodeCount"))
              (.seq
                (.assign (.var "tag") (SKYLowering.loadAt "tags" (.var "focus")))
                (switchMany (.var "tag")
                  [ (NodeTag.code .app, SKYLowering.appCase)
                  , (NodeTag.code .combK, SKYLowering.kCase)
                  , (NodeTag.code .combS, SKYLowering.sCase)
                  , (NodeTag.code .combY, SKYLowering.yCase)
                  , (NodeTag.code .oracle, SKYLowering.oracleCase) ]
                  (SKYLowering.commitAndReturn .halted)))
              (SKYLowering.commitAndReturn .halted) ])
        (enterBlockState
          (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
          [ ("tag", .int)
          , ("focus", .int)
          , ("stackSize", .int)
          , ("nodeCount", .int)
          , ("x", .int)
          , ("y", .int)
          , ("z", .int)
          , ("ref", .int) ]) =
      some (.returned (.int StepStatus.outOfHeap.code)
        (committedNodeCountState
          (skyReducerAppTagLoadedState s oracleVals hfocus)
          (layoutForState s oracleVals)
          (.int (Int.ofNat s.focus))
          (.int (Int.ofNat s.stack.length))
          (.int (Int.ofNat s.nodeCount)))) := by
    simpa [skyReducerEntryBodyStmt, skyReducerEntry, skyReducerLocals,
      skyReducerTagPrefixStmt, skyReducerTagSwitchStmt] using hentry
  rw [hbody]
  rfl

theorem execStmt_sOutOfHeap_encodeExecState_runLoweredBudget
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.maxNodes < s.nodeCount + 3)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    execStmt 400 SKYLowering.skyReducerStepDecl.body
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals) =
        some (.returned (.int StepStatus.outOfHeap.code)
          (restoreBlockState
            (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
            (committedNodeCountState
              (skyReducerAppTagLoadedState s oracleVals hfocus)
              (layoutForState s oracleVals)
              (.int (Int.ofNat s.focus))
              (.int (Int.ofNat s.stack.length))
              (.int (Int.ofNat s.nodeCount)))
            skyReducerLocals)) := by
  simpa using
    (execStmt_fuel_mono (extra := 367)
      (h := execStmt_sOutOfHeap_encodeExecState s oracleVals hwf hfocus hstack hcap hs))

theorem runLoweredStep?_sOutOfHeap
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed)
    (hfocus : s.focus < s.nodeCount) (hstack : 3 ≤ s.stack.length)
    (hcap : s.maxNodes < s.nodeCount + 3)
    (hs : (s.tags[s.focus]'hfocus) = NodeTag.code .combS) :
    runLoweredStep? s oracleVals = some (.outOfHeap, s) := by
  exact runLoweredStep?_of_execResult s oracleVals .outOfHeap s
    (restoreBlockState
      (encodeExecStateWithLayout (layoutForState s oracleVals) s oracleVals)
      (committedNodeCountState
        (skyReducerAppTagLoadedState s oracleVals hfocus)
        (layoutForState s oracleVals)
        (.int (Int.ofNat s.focus))
        (.int (Int.ofNat s.stack.length))
        (.int (Int.ofNat s.nodeCount)))
      skyReducerLocals)
    (execStmt_sOutOfHeap_encodeExecState_runLoweredBudget s oracleVals hwf hfocus hstack hcap hs)
    (by
      simpa [decodeKernelState?_restoreBlockState] using
        decodeKernelState?_committedTagLoadedState s oracleVals hwf hfocus)

private theorem node?_focus_eq_some_of_tag
    (s : State) (hwf : s.WellFormed) (hfocus : s.focus < s.nodeCount)
    {tag : NodeTag}
    (htag : NodeTag.ofCode? (s.tags[s.focus]'hfocus) = some tag) :
    s.node? s.focus =
      some
        { tag := tag
          lhs := s.lhs[s.focus]'(by
            rcases hwf with ⟨hlhs, _hrhs, _hrefs, _hnodes, _hstack⟩
            simpa [hlhs] using hfocus)
          rhs := s.rhs[s.focus]'(by
            rcases hwf with ⟨_hlhs, hrhs, _hrefs, _hnodes, _hstack⟩
            simpa [hrhs] using hfocus)
          oracleRef := s.oracleRefs[s.focus]'(by
            rcases hwf with ⟨_hlhs, _hrhs, hrefs, _hnodes, _hstack⟩
            simpa [hrefs] using hfocus) } := by
  rcases hwf with ⟨hlhs, hrhs, hrefs, _hnodes, _hstack⟩
  have hlhsFocus : s.focus < s.lhs.size := by
    simpa [hlhs] using hfocus
  have hrhsFocus : s.focus < s.rhs.size := by
    simpa [hrhs] using hfocus
  have hrefsFocus : s.focus < s.oracleRefs.size := by
    simpa [hrefs] using hfocus
  unfold State.node?
  simp [Array.getElem?_eq_getElem hfocus, Array.getElem?_eq_getElem hlhsFocus,
    Array.getElem?_eq_getElem hrhsFocus, Array.getElem?_eq_getElem hrefsFocus, htag]

private theorem node?_focus_none_of_invalidTag
    (s : State) (hfocus : s.focus < s.nodeCount)
    (htagNone : NodeTag.ofCode? (s.tags[s.focus]'hfocus) = none) :
    s.node? s.focus = none := by
  unfold State.node?
  simp [Array.getElem?_eq_getElem hfocus, htagNone]

private theorem node?_focus_none_of_outOfRange
    (s : State) (hfocus : ¬ s.focus < s.nodeCount) :
    s.node? s.focus = none := by
  have htagsLe : s.tags.size ≤ s.focus := by
    simpa [State.nodeCount, not_lt] using hfocus
  unfold State.node?
  simp [Array.getElem?_eq_none htagsLe]

private theorem code_eq_of_ofCode?_eq_some {n : Int} {tag : NodeTag}
    (h : NodeTag.ofCode? n = some tag) :
    n = tag.code := by
  by_cases h0 : n = 0
  · subst h0
    cases tag <;> simp [NodeTag.ofCode?, NodeTag.code] at h ⊢
  · by_cases h1 : n = 1
    · subst h1
      cases tag <;> simp [NodeTag.ofCode?, NodeTag.code] at h ⊢
    · by_cases h2 : n = 2
      · subst h2
        cases tag <;> simp [NodeTag.ofCode?, NodeTag.code] at h ⊢
      · by_cases h3 : n = 3
        · subst h3
          cases tag <;> simp [NodeTag.ofCode?, NodeTag.code] at h ⊢
        · by_cases h4 : n = 4
          · subst h4
            cases tag <;> simp [NodeTag.ofCode?, NodeTag.code] at h ⊢
          · have hnone : NodeTag.ofCode? n = none := by
              simp [NodeTag.ofCode?, h0, h1, h2, h3, h4]
            rw [hnone] at h
            cases h

theorem runLoweredStep?_eq_expectedStep?
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    runLoweredStep? s oracleVals = expectedStep? s oracleVals := by
  by_cases hfocus : s.focus < s.nodeCount
  · have hwf0 := hwf
    by_cases happ : (s.tags[s.focus]'hfocus) = NodeTag.code .app
    · have htag : NodeTag.ofCode? (s.tags[s.focus]'hfocus) = some .app := by
        simpa [happ] using (NodeTag.ofCode?_code .app)
      have hnode := node?_focus_eq_some_of_tag s hwf0 hfocus htag
      rw [runLoweredStep?_app s oracleVals hwf0 hfocus happ]
      simp [expectedStep?, step, hnode]
      constructor <;> rfl
    · by_cases hk : (s.tags[s.focus]'hfocus) = NodeTag.code .combK
      · have htag : NodeTag.ofCode? (s.tags[s.focus]'hfocus) = some .combK := by
          simpa [hk] using (NodeTag.ofCode?_code .combK)
        have hnode := node?_focus_eq_some_of_tag s hwf0 hfocus htag
        cases hs : s.stack with
        | nil =>
            have hstack : s.stack.length < 2 := by simp [hs]
            rw [runLoweredStep?_kShortStack s oracleVals hwf0 hfocus hstack hk]
            simp [expectedStep?, step, hnode, hs]
            constructor <;> rfl
        | cons x xs =>
            cases hs' : xs with
            | nil =>
                have hstack : s.stack.length < 2 := by simp [hs, hs']
                rw [runLoweredStep?_kShortStack s oracleVals hwf0 hfocus hstack hk]
                simp [expectedStep?, step, hnode, hs, hs']
                constructor <;> rfl
            | cons y rest =>
                have hstack : 2 ≤ s.stack.length := by simp [hs, hs']
                rw [runLoweredStep?_k s oracleVals hwf0 hfocus hstack hk]
                simp [expectedStep?, step, hnode, hs, hs']
                constructor <;> rfl
      · by_cases hsTag : (s.tags[s.focus]'hfocus) = NodeTag.code .combS
        · have htag : NodeTag.ofCode? (s.tags[s.focus]'hfocus) = some .combS := by
            simpa [hsTag] using (NodeTag.ofCode?_code .combS)
          have hnode := node?_focus_eq_some_of_tag s hwf0 hfocus htag
          cases hs : s.stack with
          | nil =>
              have hstack : s.stack.length < 3 := by simp [hs]
              rw [runLoweredStep?_sShortStack s oracleVals hwf0 hfocus hstack hsTag]
              simp [expectedStep?, step, hnode, hs]
              constructor <;> rfl
          | cons x xs =>
              cases hs' : xs with
              | nil =>
                  have hstack : s.stack.length < 3 := by simp [hs, hs']
                  rw [runLoweredStep?_sShortStack s oracleVals hwf0 hfocus hstack hsTag]
                  simp [expectedStep?, step, hnode, hs, hs']
                  constructor <;> rfl
              | cons y rest =>
                  cases hs'' : rest with
                  | nil =>
                      have hstack : s.stack.length < 3 := by simp [hs, hs', hs'']
                      rw [runLoweredStep?_sShortStack s oracleVals hwf0 hfocus hstack hsTag]
                      simp [expectedStep?, step, hnode, hs, hs', hs'']
                      constructor <;> rfl
                  | cons z rest' =>
                      have hstack : 3 ≤ s.stack.length := by simp [hs, hs', hs'']
                      have hnodes : s.nodeCount ≤ s.maxNodes := hwf0.2.2.2.1
                      have hcap : s.maxNodes < s.nodeCount + 3 ∨ s.nodeCount + 3 ≤ s.maxNodes := by
                        omega
                      cases hcap with
                      | inl hcapLt =>
                          rw [runLoweredStep?_sOutOfHeap s oracleVals hwf0 hfocus hstack hcapLt hsTag]
                          by_cases hpush0 : s.nodeCount < s.maxNodes
                          · by_cases hpush1 : s.nodeCount + 1 < s.maxNodes
                            · have hpush2 : ¬ s.nodeCount + 2 < s.maxNodes := by
                                omega
                              have hpush0' : s.tags.size < s.maxNodes := by
                                simpa [State.nodeCount] using hpush0
                              have hpush1' : s.tags.size + 1 < s.maxNodes := by
                                simpa [State.nodeCount] using hpush1
                              have hcapEq0 : s.nodeCount + 2 = s.maxNodes := by
                                omega
                              have hcapEq : s.tags.size + 2 = s.maxNodes := by
                                simpa [State.nodeCount] using hcapEq0
                              simp [expectedStep?, step, hnode, hs, hs', hs'', State.pushNode,
                                State.nodeCount, hpush0', hpush1', hcapEq]
                              constructor <;> rfl
                            · have hpush0' : s.tags.size < s.maxNodes := by
                                simpa [State.nodeCount] using hpush0
                              have hcapEq0 : s.nodeCount + 1 = s.maxNodes := by
                                omega
                              have hcapEq : s.tags.size + 1 = s.maxNodes := by
                                simpa [State.nodeCount] using hcapEq0
                              simp [expectedStep?, step, hnode, hs, hs', hs'', State.pushNode,
                                State.nodeCount, hpush0', hcapEq]
                              constructor <;> rfl
                          · have hcapEq0 : s.nodeCount = s.maxNodes := by
                              omega
                            have hcapEq : s.tags.size = s.maxNodes := by
                              simpa [State.nodeCount] using hcapEq0
                            simp [expectedStep?, step, hnode, hs, hs', hs'', State.pushNode,
                              State.nodeCount, hcapEq]
                            constructor <;> rfl
                      | inr hcapLe =>
                          have hpush0 : s.nodeCount < s.maxNodes := by
                            omega
                          have hpush1 : s.nodeCount + 1 < s.maxNodes := by
                            omega
                          have hpush2 : s.nodeCount + 2 < s.maxNodes := by
                            omega
                          have hpush0' : s.tags.size < s.maxNodes := by
                            simpa [State.nodeCount] using hpush0
                          have hpush1' : s.tags.size + 1 < s.maxNodes := by
                            simpa [State.nodeCount] using hpush1
                          have hpush2' : s.tags.size + 2 < s.maxNodes := by
                            simpa [State.nodeCount] using hpush2
                          rw [runLoweredStep?_s s oracleVals hwf0 hfocus hstack hcapLe hsTag]
                          simp [expectedStep?, step, hnode, hs, hs', hs'', skyReducerSNextState,
                            State.pushNode, State.nodeCount, hpush0', hpush1', hpush2']
                          constructor <;> rfl
        · by_cases hy : (s.tags[s.focus]'hfocus) = NodeTag.code .combY
          · have htag : NodeTag.ofCode? (s.tags[s.focus]'hfocus) = some .combY := by
              simpa [hy] using (NodeTag.ofCode?_code .combY)
            have hnode := node?_focus_eq_some_of_tag s hwf0 hfocus htag
            cases hs : s.stack with
            | nil =>
                have hstack : s.stack.length < 1 := by simp [hs]
                rw [runLoweredStep?_yShortStack s oracleVals hwf0 hfocus hstack hy]
                simp [expectedStep?, step, hnode, hs]
                constructor <;> rfl
            | cons f rest =>
                have hstack : 1 ≤ s.stack.length := by simp [hs]
                have hnodes : s.nodeCount ≤ s.maxNodes := hwf0.2.2.2.1
                have hcap : s.maxNodes < s.nodeCount + 2 ∨ s.nodeCount + 2 ≤ s.maxNodes := by
                  omega
                cases hcap with
                | inl hcapLt =>
                    rw [runLoweredStep?_yOutOfHeap s oracleVals hwf0 hfocus hstack hcapLt hy]
                    by_cases hpush0 : s.nodeCount < s.maxNodes
                    · have hpush1 : ¬ s.nodeCount + 1 < s.maxNodes := by
                        omega
                      have hpush0' : s.tags.size < s.maxNodes := by
                        simpa [State.nodeCount] using hpush0
                      have hpush1' : ¬ s.tags.size + 1 < s.maxNodes := by
                        simpa [State.nodeCount] using hpush1
                      simp [expectedStep?, step, hnode, hs, State.pushNode, State.nodeCount,
                        hpush0', hpush1']
                      constructor <;> rfl
                    · have hpush0' : ¬ s.tags.size < s.maxNodes := by
                        simpa [State.nodeCount] using hpush0
                      simp [expectedStep?, step, hnode, hs, State.pushNode, State.nodeCount, hpush0']
                      constructor <;> rfl
                | inr hcapLe =>
                    have hpush0 : s.nodeCount < s.maxNodes := by
                      omega
                    have hpush1 : s.nodeCount + 1 < s.maxNodes := by
                      omega
                    have hpush0' : s.tags.size < s.maxNodes := by
                      simpa [State.nodeCount] using hpush0
                    have hpush1' : s.tags.size + 1 < s.maxNodes := by
                      simpa [State.nodeCount] using hpush1
                    rw [runLoweredStep?_y s oracleVals hwf0 hfocus hstack hcapLe hy]
                    simp [expectedStep?, step, hnode, hs, skyReducerYNextState, State.pushNode,
                      State.nodeCount, hpush0', hpush1']
                    constructor <;> rfl
          · by_cases horacle : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle
            · have htag : NodeTag.ofCode? (s.tags[s.focus]'hfocus) = some .oracle := by
                simpa [horacle] using (NodeTag.ofCode?_code .oracle)
              have hnode := node?_focus_eq_some_of_tag s hwf0 hfocus htag
              cases hs : s.stack with
              | nil =>
                  have hstack : s.stack.length < 2 := by simp [hs]
                  rw [runLoweredStep?_oracleShortStack s oracleVals hwf0 hfocus hstack horacle]
                  simp [expectedStep?, step, hnode, hs]
                  constructor <;> rfl
              | cons t xs =>
                  cases hs' : xs with
                  | nil =>
                      have hstack : s.stack.length < 2 := by simp [hs, hs']
                      rw [runLoweredStep?_oracleShortStack s oracleVals hwf0 hfocus hstack horacle]
                      simp [expectedStep?, step, hnode, hs, hs']
                      constructor <;> rfl
                  | cons f rest =>
                      have hstack : 2 ≤ s.stack.length := by simp [hs, hs']
                      rw [runLoweredStep?_oracle s oracleVals hwf0 hfocus hstack horacle]
                      simp [expectedStep?, step, hnode, hs, hs', skyReducerOracleTargetNat,
                        oracleArrayEval_eq_getD_ne_zero]
                      constructor <;> rfl
            · have htagNone : NodeTag.ofCode? (s.tags[s.focus]'hfocus) = none := by
                cases hcode : NodeTag.ofCode? (s.tags[s.focus]'hfocus) with
                | none =>
                    rfl
                | some tag =>
                    cases tag with
                    | app =>
                        have happ' : (s.tags[s.focus]'hfocus) = NodeTag.code .app :=
                          code_eq_of_ofCode?_eq_some hcode
                        exact (happ happ').elim
                    | combK =>
                        have hk' : (s.tags[s.focus]'hfocus) = NodeTag.code .combK :=
                          code_eq_of_ofCode?_eq_some hcode
                        exact (hk hk').elim
                    | combS =>
                        have hsTag' : (s.tags[s.focus]'hfocus) = NodeTag.code .combS :=
                          code_eq_of_ofCode?_eq_some hcode
                        exact (hsTag hsTag').elim
                    | combY =>
                        have hy' : (s.tags[s.focus]'hfocus) = NodeTag.code .combY :=
                          code_eq_of_ofCode?_eq_some hcode
                        exact (hy hy').elim
                    | oracle =>
                        have horacle' : (s.tags[s.focus]'hfocus) = NodeTag.code .oracle :=
                          code_eq_of_ofCode?_eq_some hcode
                        exact (horacle horacle').elim
              have hnode := node?_focus_none_of_invalidTag s hfocus htagNone
              rw [runLoweredStep?_invalidTag s oracleVals hwf0 hfocus happ hk hsTag hy horacle]
              simp [expectedStep?, step, hnode]
              constructor <;> rfl
  · have hnode := node?_focus_none_of_outOfRange s hfocus
    rw [runLoweredStep?_focusOutOfRange s oracleVals hwf hfocus]
    simp [expectedStep?, step, hnode]
    constructor <;> rfl

theorem runLoweredFuel?_eq_expectedRunFuel?
    (fuel : Nat) (s : State) (oracleVals : Array Int)
    (hwf : s.WellFormed) :
    runLoweredFuel? fuel s oracleVals = expectedRunFuel? fuel s oracleVals := by
  induction fuel generalizing s with
  | zero =>
      rfl
  | succ fuel ih =>
      have hstepEq := runLoweredStep?_eq_expectedStep? s oracleVals hwf
      cases hstep : step (oracleArrayEval oracleVals) s with
      | mk status state =>
          cases status with
          | progress =>
              simp [expectedStep?, runLoweredFuel?, expectedRunFuel?, runFuel, hstep, hstepEq]
              have hwf' : state.WellFormed := by
                have hstepWf :
                    (step (oracleArrayEval oracleVals) s).state.WellFormed :=
                  step_wellFormed (oracleEval := oracleArrayEval oracleVals) (s := s) hwf
                simpa [hstep] using hstepWf
              exact ih state hwf'
          | halted =>
              simp [expectedStep?, runLoweredFuel?, expectedRunFuel?, runFuel, hstep, hstepEq]
          | outOfHeap =>
              simp [expectedStep?, runLoweredFuel?, expectedRunFuel?, runFuel, hstep, hstepEq]

end SKYLoweringSemantics
end Compile
end LeanCP
end HeytingLean
