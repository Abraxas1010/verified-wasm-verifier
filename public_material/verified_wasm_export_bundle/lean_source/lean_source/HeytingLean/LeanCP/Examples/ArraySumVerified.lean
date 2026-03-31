import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.VarLemmas

/-!
# LeanCP Example: Verified Array Sum

State-sensitive verification of array summation over a fixed contiguous block
of integers. The loop invariant tracks a processed prefix, the remaining suffix,
the current index, and the accumulated prefix sum while keeping the array
contents unchanged.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

/-- Read-only state-sensitive array predicate for contiguous integer cells. -/
def arrayAt_s (base : Nat) (vals : List Int) : SProp := fun st =>
  ∀ i v, vals[i]? = some v → st.heap.read (base + i) = some (.int v)

private theorem arrayAt_s_updateVar (base : Nat) (vals : List Int) (st : CState)
    (x : String) (v : CVal) :
    arrayAt_s base vals (st.updateVar x v) ↔ arrayAt_s base vals st := by
  rfl

private theorem array_sum_step (done : List Int) (h : Int) :
    (done ++ [h]).sum = done.sum + h := by
  simp

def arraySumCond : CExpr :=
  .binop .lt (.var "i") (.var "n")

def arraySumLoopBody : CStmt :=
  .seq
    (.assign (.var "s")
      (.binop .add (.var "s")
        (.deref (.binop .add (.var "a") (.var "i")))))
    (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))

def arraySumProgram : CStmt :=
  .seq (.assign (.var "s") (.intLit 0))
    (.seq (.assign (.var "i") (.intLit 0))
      (.seq (.whileInv arraySumCond HProp.htrue arraySumLoopBody)
        (.ret (.var "s"))))

def arraySumInv (vals : List Int) (base : Nat) : SProp := fun st =>
  ∃ done rest,
    vals = done ++ rest ∧
    st.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) ∧
    st.lookupVar "n" = some (.int (Int.ofNat vals.length)) ∧
    st.lookupVar "i" = some (.int (Int.ofNat done.length)) ∧
    st.lookupVar "s" = some (.int done.sum) ∧
    arrayAt_s base vals st

def arraySumLoopPost (vals : List Int) (base : Nat) : CVal → SProp := fun _ st =>
  st.lookupVar "s" = some (.int vals.sum) ∧
  arrayAt_s base vals st

private theorem arraySum_loopFree : LoopFree arraySumLoopBody := by
  simp [arraySumLoopBody, LoopFree]

private theorem arraySum_noReturn : NoReturn arraySumLoopBody := by
  simp [arraySumLoopBody, NoReturn]

private theorem arraySum_loop_from_state
    (vals done rest : List Int) (base : Nat) (st : CState)
    (hvals : vals = done ++ rest)
    (ha : st.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)))
    (hn : st.lookupVar "n" = some (.int (Int.ofNat vals.length)))
    (hi : st.lookupVar "i" = some (.int (Int.ofNat done.length)))
    (hs : st.lookupVar "s" = some (.int done.sum))
    (harray : arrayAt_s base vals st) :
    swhileWP rest.length arraySumCond (arraySumInv vals base) arraySumLoopBody (arraySumLoopPost vals base) st := by
  induction rest generalizing done st with
  | nil =>
      have hInv : arraySumInv vals base st := by
        exact ⟨done, [], hvals, ha, hn, hi, hs, harray⟩
      have hdone : vals = done := by simpa using hvals
      have hCond : evalExpr arraySumCond st = some (.int 0) := by
        simpa [arraySumCond, evalExpr, evalStaticExpr, hi, hn, hvals] using
          (show evalBinOp .lt (.int (Int.ofNat done.length)) (.int (Int.ofNat done.length)) =
              some (.int 0) by
            change some (CVal.int (if Int.ofNat done.length < Int.ofNat done.length then 1 else 0)) =
              some (CVal.int 0)
            simp)
      have hPost : arraySumLoopPost vals base CVal.undef st := by
        refine ⟨?_, harray⟩
        simpa [hdone] using hs
      simpa [swhileWP, hCond, isTruthy] using And.intro hInv hPost
  | cons h tail ih =>
      have hInv : arraySumInv vals base st := by
        exact ⟨done, h :: tail, hvals, ha, hn, hi, hs, harray⟩
      have hltNat : done.length < vals.length := by
        rw [hvals]
        simp
      have hCond : evalExpr arraySumCond st = some (.int 1) := by
        have hltEval :
            evalBinOp .lt (.int (Int.ofNat done.length)) (.int (Int.ofNat vals.length)) =
              some (.int 1) := by
          change some (CVal.int (if Int.ofNat done.length < Int.ofNat vals.length then 1 else 0)) =
            some (CVal.int 1)
          have hlt : Int.ofNat done.length < Int.ofNat vals.length := Int.ofNat_lt.mpr hltNat
          rw [if_pos hlt]
        simpa [arraySumCond, evalExpr, evalStaticExpr, hi, hn] using hltEval
      have hGetHead : vals[done.length]? = some h := by
        rw [hvals]
        simp
      have hReadHead : st.heap.read (base + done.length) = some (.int h) := by
        exact harray done.length h hGetHead
      have hEvalPtr :
          evalExpr (.binop .add (.var "a") (.var "i")) st =
            some (CVal.ptrAddr ((base + done.length) : PtrVal)) := by
        simpa [evalExpr, evalStaticExpr, ha, hi] using
          (show evalBinOp .add (CVal.ptrAddr (base : PtrVal)) (.int (Int.ofNat done.length)) =
              some (CVal.ptrAddr ((base + done.length) : PtrVal)) by
            change (if 0 ≤ Int.ofNat done.length then
                some (CVal.ptrAddr { block := 0, offset := Int.ofNat base + Int.ofNat done.length })
              else none) = some (CVal.ptrAddr ((base + done.length) : PtrVal))
            simp)
      have hReadPtrHead : st.readPtr (base + done.length) = some (.int h) := by
        simpa [hReadHead] using (CState.readPtr_block0 st (base + done.length) (base + done.length))
      have hEvalDeref : evalExpr (.deref (.binop .add (.var "a") (.var "i"))) st = some (.int h) := by
        simpa [evalExpr, evalStaticExpr, hEvalPtr] using hReadPtrHead
      have hEvalSum : evalExpr (.binop .add (.var "s") (.deref (.binop .add (.var "a") (.var "i")))) st =
          some (.int (done.sum + h)) := by
        simpa [evalExpr, evalStaticExpr, hs, hEvalDeref] using
          (show evalBinOp .add (.int done.sum) (.int h) = some (.int (done.sum + h)) by
            rfl)
      let st1 := st.updateVar "s" (.int (done.sum + h))
      let st2 := st1.updateVar "i" (.int (Int.ofNat (done.length + 1)))

      have ha1 : st1.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) := by
        calc
          st1.lookupVar "a" = st.lookupVar "a" := by
            simpa [st1] using lookupVar_updateVar_ne st "s" "a" (.int (done.sum + h)) (by decide : "a" ≠ "s")
          _ = some (CVal.ptrAddr (base : PtrVal)) := ha
      have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
        calc
          st1.lookupVar "n" = st.lookupVar "n" := by
            simpa [st1] using lookupVar_updateVar_ne st "s" "n" (.int (done.sum + h)) (by decide : "n" ≠ "s")
          _ = some (.int (Int.ofNat vals.length)) := hn
      have ha2 : st2.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) := by
        calc
          st2.lookupVar "a" = st1.lookupVar "a" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "i" "a" (.int (Int.ofNat (done.length + 1))) (by decide : "a" ≠ "i")
          _ = some (CVal.ptrAddr (base : PtrVal)) := ha1
      have hn2 : st2.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
        calc
          st2.lookupVar "n" = st1.lookupVar "n" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "i" "n" (.int (Int.ofNat (done.length + 1))) (by decide : "n" ≠ "i")
          _ = some (.int (Int.ofNat vals.length)) := hn1
      have hi2 : st2.lookupVar "i" = some (.int (Int.ofNat ((done ++ [h]).length))) := by
        simpa [st2] using lookupVar_updateVar_eq st1 "i" (.int (Int.ofNat (done.length + 1)))
      have hs2 : st2.lookupVar "s" = some (.int ((done ++ [h]).sum)) := by
        calc
          st2.lookupVar "s" = st1.lookupVar "s" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "i" "s" (.int (Int.ofNat (done.length + 1))) (by decide : "s" ≠ "i")
          _ = some (.int (done.sum + h)) := by
            simpa [st1] using lookupVar_updateVar_eq st "s" (.int (done.sum + h))
          _ = some (.int ((done ++ [h]).sum)) := by
            simp
      have harray1 : arrayAt_s base vals st1 := by
        simpa [st1] using (arrayAt_s_updateVar base vals st "s" (.int (done.sum + h))).2 harray
      have harray2 : arrayAt_s base vals st2 := by
        simpa [st2] using (arrayAt_s_updateVar base vals st1 "i" (.int (Int.ofNat (done.length + 1)))).2 harray1
      have hvals2 : vals = (done ++ [h]) ++ tail := by
        simpa [List.append_assoc] using hvals
      have hLoop2 :
          swhileWP tail.length arraySumCond (arraySumInv vals base) arraySumLoopBody (arraySumLoopPost vals base) st2 := by
        exact ih (done ++ [h]) st2 hvals2 ha2 hn2 hi2 hs2 harray2

      have hi1 : st1.lookupVar "i" = some (.int (Int.ofNat done.length)) := by
        calc
          st1.lookupVar "i" = st.lookupVar "i" := by
            simpa [st1] using lookupVar_updateVar_ne st "s" "i" (.int (done.sum + h)) (by decide : "i" ≠ "s")
          _ = some (.int (Int.ofNat done.length)) := hi
      have hEvalI1 : evalExpr (.binop .add (.var "i") (.intLit 1)) st1 =
          some (.int (Int.ofNat (done.length + 1))) := by
        simpa [evalExpr, evalStaticExpr, hi1] using
          (show evalBinOp .add (.int (Int.ofNat done.length)) (.int 1) =
              some (.int (Int.ofNat (done.length + 1))) by
            change some (CVal.int (Int.ofNat done.length + 1)) =
              some (CVal.int (Int.ofNat (done.length + 1)))
            simp)
      have hAssignI :
          swp (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
            (fun _ => swhileWP tail.length arraySumCond (arraySumInv vals base) arraySumLoopBody (arraySumLoopPost vals base)) st1 := by
        simpa [swp, hEvalI1, st2] using hLoop2
      have hBody :
          swp arraySumLoopBody
            (fun _ => swhileWP tail.length arraySumCond (arraySumInv vals base) arraySumLoopBody (arraySumLoopPost vals base)) st := by
        simpa [arraySumLoopBody, swp, hEvalSum, st1] using hAssignI
      simpa [swhileWP, hCond] using And.intro hInv hBody

theorem arraySum_correct (vals : List Int) (base : Nat) :
    ∀ st,
      st.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) →
      st.lookupVar "n" = some (.int (Int.ofNat vals.length)) →
      arrayAt_s base vals st →
      ∃ st',
        execStmt (swhileFuel arraySumLoopBody vals.length + 3) arraySumProgram st =
          some (.returned (.int vals.sum) st') ∧
        arrayAt_s base vals st' := by
  intro st ha hn harray
  let st1 := st.updateVar "s" (.int 0)
  let st2 := st1.updateVar "i" (.int 0)

  have ha1 : st1.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) := by
    calc
      st1.lookupVar "a" = st.lookupVar "a" := by
        simpa [st1] using lookupVar_updateVar_ne st "s" "a" (.int 0) (by decide : "a" ≠ "s")
      _ = some (CVal.ptrAddr (base : PtrVal)) := ha
  have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
    calc
      st1.lookupVar "n" = st.lookupVar "n" := by
        simpa [st1] using lookupVar_updateVar_ne st "s" "n" (.int 0) (by decide : "n" ≠ "s")
      _ = some (.int (Int.ofNat vals.length)) := hn
  have ha2 : st2.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) := by
    calc
      st2.lookupVar "a" = st1.lookupVar "a" := by
        simpa [st2] using lookupVar_updateVar_ne st1 "i" "a" (.int 0) (by decide : "a" ≠ "i")
      _ = some (CVal.ptrAddr (base : PtrVal)) := ha1
  have hn2 : st2.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
    calc
      st2.lookupVar "n" = st1.lookupVar "n" := by
        simpa [st2] using lookupVar_updateVar_ne st1 "i" "n" (.int 0) (by decide : "n" ≠ "i")
      _ = some (.int (Int.ofNat vals.length)) := hn1
  have hi2 : st2.lookupVar "i" = some (.int 0) := by
    simpa [st2] using lookupVar_updateVar_eq st1 "i" (.int 0)
  have hs2 : st2.lookupVar "s" = some (.int 0) := by
    calc
      st2.lookupVar "s" = st1.lookupVar "s" := by
        simpa [st2] using lookupVar_updateVar_ne st1 "i" "s" (.int 0) (by decide : "s" ≠ "i")
      _ = some (.int 0) := by
        simpa [st1] using lookupVar_updateVar_eq st "s" (.int 0)
  have harray1 : arrayAt_s base vals st1 := by
    simpa [st1] using (arrayAt_s_updateVar base vals st "s" (.int 0)).2 harray
  have harray2 : arrayAt_s base vals st2 := by
    simpa [st2] using (arrayAt_s_updateVar base vals st1 "i" (.int 0)).2 harray1

  have hLoopWP :
      swhileWP vals.length arraySumCond (arraySumInv vals base) arraySumLoopBody (arraySumLoopPost vals base) st2 := by
    exact arraySum_loop_from_state vals [] vals base st2 (by simp) ha2 hn2 hi2 hs2 harray2
  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel arraySumLoopBody vals.length)
          (.whileInv arraySumCond HProp.htrue arraySumLoopBody) st2 = some (.normal stLoop) ∧
        arraySumLoopPost vals base CVal.undef stLoop := by
    exact swhileWP_sound arraySumCond (arraySumInv vals base) HProp.htrue arraySumLoopBody
      arraySum_loopFree arraySum_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨hsLoop, harrayLoop⟩

  have hRet :
      execStmt (swhileFuel arraySumLoopBody vals.length) (.ret (.var "s")) stLoop =
        some (.returned (.int vals.sum) stLoop) := by
    change execStmt (Nat.succ (stmtDepth arraySumLoopBody + vals.length)) (.ret (.var "s")) stLoop =
      some (.returned (.int vals.sum) stLoop)
    simp [execStmt, evalExpr, evalStaticExpr, hsLoop]
  let loopFuel := swhileFuel arraySumLoopBody vals.length
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv arraySumCond HProp.htrue arraySumLoopBody) (.ret (.var "s"))) st2 =
          some (.returned (.int vals.sum) stLoop) := by
    change execStmt (loopFuel + 1)
      (.seq (.whileInv arraySumCond HProp.htrue arraySumLoopBody) (.ret (.var "s"))) st2 =
        some (.returned (.int vals.sum) stLoop)
    simp [execStmt]
    rw [hExecLoop]
    simpa [hRet]
  have hExecRest :
      execStmt (loopFuel + 2)
        (.seq (.assign (.var "i") (.intLit 0))
          (.seq (.whileInv arraySumCond HProp.htrue arraySumLoopBody) (.ret (.var "s")))) st1 =
          some (.returned (.int vals.sum) stLoop) := by
    change execStmt (Nat.succ (loopFuel + 1))
      (.seq (.assign (.var "i") (.intLit 0))
        (.seq (.whileInv arraySumCond HProp.htrue arraySumLoopBody) (.ret (.var "s")))) st1 =
          some (.returned (.int vals.sum) stLoop)
    simpa [execStmt, st2] using hExecInner
  refine ⟨stLoop, ?_, harrayLoop⟩
  change execStmt (Nat.succ (loopFuel + 2)) arraySumProgram st =
    some (.returned (.int vals.sum) stLoop)
  simpa [arraySumProgram, execStmt, st1] using hExecRest

end HeytingLean.LeanCP.Examples
