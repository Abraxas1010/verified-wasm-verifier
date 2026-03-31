import HeytingLean.LeanCP.Examples.Strlen
import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Lang.CSemanticsDecEq
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

/-- Read-only state-sensitive string predicate for a null-terminated character
array stored contiguously from `base`. -/
def stringAt_s (base : Nat) (chars : List Int) : SProp := fun st =>
  ∀ i v, (chars ++ [0])[i]? = some v → st.heap.read (base + i) = some (.int v)

private theorem stringAt_s_updateVar (base : Nat) (chars : List Int) (st : CState)
    (x : String) (v : CVal) :
    stringAt_s base chars (st.updateVar x v) ↔ stringAt_s base chars st := by
  rfl

def strlenCond : CExpr :=
  .binop .ne (.deref (.var "s")) (.intLit 0)

def strlenLoopBody : CStmt :=
  .seq
    (.assign (.var "s") (.binop .add (.var "s") (.intLit 1)))
    (.assign (.var "len") (.binop .add (.var "len") (.intLit 1)))

def strlenInv (chars : List Int) (base : Nat) : SProp := fun st =>
  ∃ done rest,
    chars = done ++ rest ∧
    st.lookupVar "s" = some (CVal.ptrAddr ((base + done.length) : PtrVal)) ∧
    st.lookupVar "len" = some (.int (Int.ofNat done.length)) ∧
    stringAt_s base chars st

def strlenLoopPost (chars : List Int) (base : Nat) : CVal → SProp := fun _ st =>
  st.lookupVar "len" = some (.int (Int.ofNat chars.length)) ∧
  stringAt_s base chars st

private theorem strlen_loopFree : LoopFree strlenLoopBody := by
  simp [strlenLoopBody, LoopFree]

private theorem strlen_noReturn : NoReturn strlenLoopBody := by
  simp [strlenLoopBody, NoReturn]

private theorem strlen_loop_from_state
    (chars done rest : List Int) (base : Nat) (st : CState)
    (hchars : chars = done ++ rest)
    (hs : st.lookupVar "s" = some (CVal.ptrAddr ((base + done.length) : PtrVal)))
    (hlen : st.lookupVar "len" = some (.int (Int.ofNat done.length)))
    (hstring : stringAt_s base chars st)
    (hnz : ∀ (i : Nat) c, chars[i]? = some c → c ≠ 0) :
    swhileWP rest.length strlenCond (strlenInv chars base) strlenLoopBody (strlenLoopPost chars base) st := by
  induction rest generalizing done st with
  | nil =>
      have hInv : strlenInv chars base st := by
        exact ⟨done, [], hchars, hs, hlen, hstring⟩
      have hdone : chars = done := by
        simpa using hchars
      have hReadZero : st.heap.read (base + done.length) = some (.int 0) := by
        exact hstring done.length 0 (by simpa [hdone])
      have hReadPtrZero : st.readPtr (base + done.length) = some (.int 0) := by
        simpa [hReadZero] using (CState.readPtr_block0 st (base + done.length) (base + done.length))
      have hEvalS : evalExpr (.var "s") st = some (CVal.ptrAddr ((base + done.length) : PtrVal)) := by
        simpa [evalExpr, evalStaticExpr] using hs
      have hEvalDeref : evalExpr (.deref (.var "s")) st = some (.int 0) := by
        simpa [evalExpr, evalStaticExpr, hEvalS] using hReadPtrZero
      have hCond : evalExpr strlenCond st = some (.int 0) := by
        simpa [strlenCond, evalExpr, evalStaticExpr, hEvalDeref] using
          (show evalBinOp .ne (.int 0) (.int 0) = some (.int 0) by
            change some (CVal.int (if (0 : Int) ≠ 0 then 1 else 0)) = some (CVal.int 0)
            simp)
      have hPost : strlenLoopPost chars base CVal.undef st := by
        refine ⟨?_, hstring⟩
        simpa [hdone] using hlen
      simpa [swhileWP, hCond, isTruthy] using And.intro hInv hPost
  | cons h tail ih =>
      have hInv : strlenInv chars base st := by
        exact ⟨done, h :: tail, hchars, hs, hlen, hstring⟩
      have hHeadIndex : chars[done.length]? = some h := by
        rw [hchars]
        simp
      have hneZero : h ≠ 0 := hnz done.length h hHeadIndex
      have hReadHead : st.heap.read (base + done.length) = some (.int h) := by
        exact hstring done.length h (by simpa [hchars])
      have hReadPtrHead : st.readPtr (base + done.length) = some (.int h) := by
        simpa [hReadHead] using (CState.readPtr_block0 st (base + done.length) (base + done.length))
      have hEvalS : evalExpr (.var "s") st = some (CVal.ptrAddr ((base + done.length) : PtrVal)) := by
        simpa [evalExpr, evalStaticExpr] using hs
      have hEvalDeref : evalExpr (.deref (.var "s")) st = some (.int h) := by
        simpa [evalExpr, evalStaticExpr, hEvalS] using hReadPtrHead
      have hCond : evalExpr strlenCond st = some (.int 1) := by
        simpa [strlenCond, evalExpr, evalStaticExpr, hEvalDeref] using
          (show evalBinOp .ne (.int h) (.int 0) = some (.int 1) by
            change some (CVal.int (if h ≠ 0 then 1 else 0)) = some (CVal.int 1)
            simp [hneZero])
      have hEvalNextS :
          evalExpr (.binop .add (.var "s") (.intLit 1)) st =
            some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) := by
        simpa [evalExpr, evalStaticExpr, hs] using
          (show evalBinOp .add (CVal.ptrAddr (((base + done.length : Nat)) : PtrVal)) (.int 1) =
              some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) by
            change
              (if 0 ≤ (1 : Int) then
                some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + done.length) + 1 })
              else none) =
                some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })
            simpa [Int.add_assoc])
      let st1 := st.updateVar "s" (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })
      let st2 := st1.updateVar "len" (.int (Int.ofNat (done.length + 1)))
      have hs1 : st1.lookupVar "s" = some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) := by
        simpa [st1] using lookupVar_updateVar_eq st "s"
          (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })
      have hlen_ne_s : "len" ≠ "s" := by
        simp
      have hlen1 : st1.lookupVar "len" = some (.int (Int.ofNat done.length)) := by
        calc
          st1.lookupVar "len" = st.lookupVar "len" := by
            simpa [st1] using lookupVar_updateVar_ne st "s" "len"
              (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })
              hlen_ne_s
          _ = some (.int (Int.ofNat done.length)) := hlen
      have hs_ne_len : "s" ≠ "len" := by
        simp
      have hs2 : st2.lookupVar "s" = some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) := by
        calc
          st2.lookupVar "s" = st1.lookupVar "s" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "len" "s" (.int (Int.ofNat (done.length + 1))) hs_ne_len
          _ = some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) := hs1
      have hlen2 : st2.lookupVar "len" = some (.int (Int.ofNat ((done ++ [h]).length))) := by
        simpa [st2] using lookupVar_updateVar_eq st1 "len" (.int (Int.ofNat (done.length + 1)))
      have hstring1 : stringAt_s base chars st1 := by
        simpa [st1] using (stringAt_s_updateVar base chars st "s"
          (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })).2 hstring
      have hstring2 : stringAt_s base chars st2 := by
        simpa [st2] using (stringAt_s_updateVar base chars st1 "len" (.int (Int.ofNat (done.length + 1)))).2 hstring1
      have hchars2 : chars = (done ++ [h]) ++ tail := by
        simpa [List.append_assoc] using hchars
      have hLoop2 :
          swhileWP tail.length strlenCond (strlenInv chars base) strlenLoopBody (strlenLoopPost chars base) st2 := by
        exact ih (done ++ [h]) st2 hchars2 hs2 hlen2 hstring2
      have hEvalLenInc :
          evalExpr (.binop .add (.var "len") (.intLit 1)) st1 =
            some (.int (Int.ofNat (done.length + 1))) := by
        simpa [evalExpr, evalStaticExpr, hlen1] using
          (show evalBinOp .add (.int (Int.ofNat done.length)) (.int 1) =
              some (.int (Int.ofNat (done.length + 1))) by
            change some (CVal.int (Int.ofNat done.length + 1)) =
              some (CVal.int (Int.ofNat (done.length + 1)))
            simp)
      have hAssignLen :
          swp (.assign (.var "len") (.binop .add (.var "len") (.intLit 1)))
            (fun _ => swhileWP tail.length strlenCond (strlenInv chars base) strlenLoopBody (strlenLoopPost chars base)) st1 := by
        simpa [swp, hEvalLenInc, st2] using hLoop2
      have hBody :
          swp strlenLoopBody
            (fun _ => swhileWP tail.length strlenCond (strlenInv chars base) strlenLoopBody (strlenLoopPost chars base)) st := by
        simpa [strlenLoopBody, swp, hEvalNextS, st1] using hAssignLen
      simpa [swhileWP, hCond] using And.intro hInv hBody

theorem strlen_correct (chars : List Int) (base : Nat) :
    ∀ st,
      st.lookupVar "s" = some (CVal.ptrAddr (base : PtrVal)) →
      stringAt_s base chars st →
      (∀ (i : Nat) c, chars[i]? = some c → c ≠ 0) →
      ∃ st',
        execStmt (swhileFuel strlenLoopBody chars.length + 2) strlenBody st =
          some (.returned (.int (Int.ofNat chars.length)) st') ∧
        stringAt_s base chars st' := by
  intro st hs hstring hnz
  let st1 := st.updateVar "len" (.int 0)
  have hs_ne_len : "s" ≠ "len" := by
    simp
  have hs1 : st1.lookupVar "s" = some (CVal.ptrAddr (base : PtrVal)) := by
    calc
      st1.lookupVar "s" = st.lookupVar "s" := by
        simpa [st1] using lookupVar_updateVar_ne st "len" "s" (.int 0) hs_ne_len
      _ = some (CVal.ptrAddr (base : PtrVal)) := hs
  have hlen1 : st1.lookupVar "len" = some (.int 0) := by
    simpa [st1] using lookupVar_updateVar_eq st "len" (.int 0)
  have hstring1 : stringAt_s base chars st1 := by
    simpa [st1] using (stringAt_s_updateVar base chars st "len" (.int 0)).2 hstring
  have hLoopWP :
      swhileWP chars.length strlenCond (strlenInv chars base) strlenLoopBody (strlenLoopPost chars base) st1 := by
    exact strlen_loop_from_state chars [] chars base st1 (by simp) hs1 hlen1 hstring1 hnz
  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel strlenLoopBody chars.length)
          (.whileInv strlenCond HProp.htrue strlenLoopBody) st1 = some (.normal stLoop) ∧
        strlenLoopPost chars base CVal.undef stLoop := by
    exact swhileWP_sound strlenCond (strlenInv chars base) HProp.htrue strlenLoopBody
      strlen_loopFree strlen_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨hlenLoop, hstringLoop⟩
  have hRet :
      execStmt (swhileFuel strlenLoopBody chars.length) (.ret (.var "len")) stLoop =
        some (.returned (.int (Int.ofNat chars.length)) stLoop) := by
    change execStmt (Nat.succ (stmtDepth strlenLoopBody + chars.length)) (.ret (.var "len")) stLoop =
      some (.returned (.int (Int.ofNat chars.length)) stLoop)
    simp [execStmt, hlenLoop]
  let loopFuel := swhileFuel strlenLoopBody chars.length
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv strlenCond HProp.htrue strlenLoopBody) (.ret (.var "len"))) st1 =
          some (.returned (.int (Int.ofNat chars.length)) stLoop) := by
    change execStmt (loopFuel + 1)
      (.seq (.whileInv strlenCond HProp.htrue strlenLoopBody) (.ret (.var "len"))) st1 =
        some (.returned (.int (Int.ofNat chars.length)) stLoop)
    simp [execStmt]
    rw [hExecLoop]
    simpa [hRet]
  refine ⟨stLoop, ?_, hstringLoop⟩
  change execStmt (Nat.succ (loopFuel + 1)) strlenBody st =
    some (.returned (.int (Int.ofNat chars.length)) stLoop)
  simpa [strlenBody, strlenCond, strlenLoopBody, execStmt, st1] using hExecInner

def strlenInit : CState :=
  { heap := (((Heap.empty.write 100 (.int 1)).write 101 (.int 2)).write 102 (.int 0))
    env := [("s", .ptr 0 100)]
    nextAddr := 200 }

def strlenFinal : CState :=
  { heap := (((Heap.empty.write 100 (.int 1)).write 101 (.int 2)).write 102 (.int 0))
    env := [("len", .int 2), ("s", .ptr 0 102)]
    nextAddr := 200 }

theorem strlen_executes :
    execStmt 16 strlenBody strlenInit = some (.returned (.int 2) strlenFinal) := by
  native_decide

theorem strlen_verified :
    ∃ st',
      execStmt (swhileFuel strlenLoopBody 2 + 2) strlenBody strlenInit =
        some (.returned (.int 2) st') ∧
      stringAt_s 100 [1, 2] st' := by
  refine strlen_correct [1, 2] 100 strlenInit ?_ ?_ ?_
  · rfl
  · intro i v hv
    cases i with
    | zero =>
        simp [strlenInit, Heap.read, Heap.write, Finmap.lookup_insert] at hv ⊢
        simpa using hv
    | succ i =>
        cases i with
        | zero =>
            simp [strlenInit, Heap.read, Heap.write, Finmap.lookup_insert, Finmap.lookup_insert_of_ne] at hv ⊢
            simpa using hv
        | succ i =>
            cases i with
            | zero =>
                simp [strlenInit, Heap.read, Heap.write, Finmap.lookup_insert] at hv ⊢
                simpa using hv
            | succ i =>
                simp at hv
  · intro i c hc
    cases i with
    | zero =>
        simp at hc
        subst c
        decide
    | succ i =>
        cases i with
        | zero =>
            simp at hc
            subst c
            decide
        | succ i =>
            simp at hc

theorem strlen_heap_preserved :
    ∃ st',
      execStmt 16 strlenBody strlenInit = some (.returned (.int 2) st') ∧
      st'.heap.read 100 = some (.int 1) ∧
      st'.heap.read 101 = some (.int 2) ∧
      st'.heap.read 102 = some (.int 0) := by
  refine ⟨strlenFinal, strlen_executes, ?_, ?_, ?_⟩ <;>
    simp [strlenFinal]

theorem strlen_forward_verified :
    swp (.assign (.var "len") (.intLit 0))
      (fun _ st => st.lookupVar "len" = some (.int 0))
      strlenInit := by
  xstep
  xentailer

end HeytingLean.LeanCP.Examples
