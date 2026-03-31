import HeytingLean.LeanCP.RealWorld.Support
import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.VarLemmas
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

def memsetCond : CExpr :=
  .binop .lt (.var "i") (.var "n")

def memsetLoopBody : CStmt :=
  .seq
    (.assign (.deref (.binop .add (.var "dst") (.var "i"))) (.var "value"))
    (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))

def memsetBody : CStmt :=
  .seq (.assign (.var "i") (.intLit 0))
    (.seq (.whileInv memsetCond HProp.htrue memsetLoopBody)
      (.ret (.var "dst")))

def memsetInv (base n : Nat) (fill : Int) : SProp := fun st =>
  ∃ k,
    k ≤ n ∧
    st.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) ∧
    st.lookupVar "value" = some (.int fill) ∧
    st.lookupVar "n" = some (.int (Int.ofNat n)) ∧
    st.lookupVar "i" = some (.int (Int.ofNat k)) ∧
    allocated_s base n st ∧
    filled_s base k fill st

def memsetLoopPost (base n : Nat) (fill : Int) : CVal → SProp := fun _ st =>
  st.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) ∧
  st.lookupVar "i" = some (.int (Int.ofNat n)) ∧
  filled_s base n fill st

private theorem memset_loopFree : LoopFree memsetLoopBody := by
  simp [memsetLoopBody, LoopFree]

private theorem memset_noReturn : NoReturn memsetLoopBody := by
  simp [memsetLoopBody, NoReturn]

private theorem memset_loop_from_state
    (base n : Nat) (fill : Int) :
    ∀ rem k st,
      n = k + rem →
      st.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) →
      st.lookupVar "value" = some (.int fill) →
      st.lookupVar "n" = some (.int (Int.ofNat n)) →
      st.lookupVar "i" = some (.int (Int.ofNat k)) →
      allocated_s base n st →
      filled_s base k fill st →
      swhileWP rem memsetCond (memsetInv base n fill) memsetLoopBody
        (memsetLoopPost base n fill) st := by
  intro rem
  induction rem with
  | zero =>
      intro k st hk hdst hval hn hi halloc hfilled
      have hkEq : k = n := by omega
      have hInv : memsetInv base n fill st := by
        refine ⟨k, ?_, hdst, hval, hn, hi, halloc, hfilled⟩
        omega
      have hCond : evalExpr memsetCond st = some (.int 0) := by
        simpa [memsetCond, evalExpr, evalStaticExpr, hi, hn, hkEq] using
          (show evalBinOp .lt (.int (Int.ofNat n)) (.int (Int.ofNat n)) = some (.int 0) by
            change some (CVal.int (if Int.ofNat n < Int.ofNat n then 1 else 0)) =
              some (CVal.int 0)
            simp)
      have hPost : memsetLoopPost base n fill CVal.undef st := by
        refine ⟨hdst, ?_, ?_⟩
        simpa [hkEq] using hi
        simpa [hkEq] using hfilled
      simpa [swhileWP, hCond, isTruthy] using And.intro hInv hPost
  | succ rem ih =>
      intro k st hk hdst hval hn hi halloc hfilled
      have hklt : k < n := by omega
      have hInv : memsetInv base n fill st := by
        refine ⟨k, ?_, hdst, hval, hn, hi, halloc, hfilled⟩
        omega
      have hBin :
          evalBinOp .lt (.int (Int.ofNat k)) (.int (Int.ofNat n)) =
            some (.int 1) := by
        change some (CVal.int (if Int.ofNat k < Int.ofNat n then 1 else 0)) =
          some (CVal.int 1)
        have hlt : Int.ofNat k < Int.ofNat n := Int.ofNat_lt.mpr hklt
        rw [if_pos hlt]
      have hCond : evalExpr memsetCond st = some (.int 1) := by
        simpa [memsetCond, evalExpr, evalStaticExpr, hi, hn] using hBin
      have hEvalPtr :
          evalExpr (.binop .add (.var "dst") (.var "i")) st =
            some (CVal.ptrAddr ((base + k) : PtrVal)) := by
        simpa [evalExpr, evalStaticExpr, hdst, hi] using
          (show evalBinOp .add (CVal.ptrAddr (base : PtrVal)) (.int (Int.ofNat k)) =
              some (CVal.ptrAddr ((base + k) : PtrVal)) by
            change
              (if 0 ≤ Int.ofNat k then
                some (CVal.ptrAddr { block := 0, offset := Int.ofNat base + Int.ofNat k })
              else none) = some (CVal.ptrAddr ((base + k) : PtrVal))
            simp)
      have hEvalWrite : evalExpr (.var "value") st = some (.int fill) := by
        simpa [evalExpr] using hval
      rcases halloc k hklt with ⟨old, hold⟩
      have hReadPtr : st.readPtr ((base + k) : PtrVal) = some old := by
        simpa [hold] using CState.readPtr_block0 st (base + k) (base + k)
      let st1 : CState := st.withHeap (st.heap.write (base + k) (.int fill))
      have hWritePtr :
          st.writePtr ((base + k) : PtrVal) (.int fill) = some st1 := by
        simpa [st1] using CState.writePtr_block0 st (base + k) (base + k) (.int fill)
      have hdst1 : st1.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) := by
        simpa [st1, CState.lookupVar, CState.withHeap] using hdst
      have hval1 : st1.lookupVar "value" = some (.int fill) := by
        simpa [st1, CState.lookupVar, CState.withHeap] using hval
      have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat n)) := by
        simpa [st1, CState.lookupVar, CState.withHeap] using hn
      have hi1 : st1.lookupVar "i" = some (.int (Int.ofNat k)) := by
        simpa [st1, CState.lookupVar, CState.withHeap] using hi
      have halloc1 : allocated_s base n st1 := by
        exact allocated_s_write_preserved st base n (base + k) (.int fill) halloc
      have hfilled1 : filled_s base (k + 1) fill st1 := by
        exact filled_s_succ_of_write st base k fill hfilled
      let st2 := st1.updateVar "i" (.int (Int.ofNat (k + 1)))
      have hstep : n = (k + 1) + rem := by omega
      have hdst2 : st2.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) := by
        calc
          st2.lookupVar "dst" = st1.lookupVar "dst" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "i" "dst" (.int (Int.ofNat (k + 1)))
              (by decide : "dst" ≠ "i")
          _ = some (CVal.ptrAddr (base : PtrVal)) := hdst1
      have hval2 : st2.lookupVar "value" = some (.int fill) := by
        calc
          st2.lookupVar "value" = st1.lookupVar "value" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "i" "value" (.int (Int.ofNat (k + 1)))
              (by decide : "value" ≠ "i")
          _ = some (.int fill) := hval1
      have hn2 : st2.lookupVar "n" = some (.int (Int.ofNat n)) := by
        calc
          st2.lookupVar "n" = st1.lookupVar "n" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "i" "n" (.int (Int.ofNat (k + 1)))
              (by decide : "n" ≠ "i")
          _ = some (.int (Int.ofNat n)) := hn1
      have hi2 : st2.lookupVar "i" = some (.int (Int.ofNat (k + 1))) := by
        simpa [st2] using lookupVar_updateVar_eq st1 "i" (.int (Int.ofNat (k + 1)))
      have halloc2 : allocated_s base n st2 := by
        simpa [st2] using (allocated_s_updateVar base n st1 "i" (.int (Int.ofNat (k + 1)))).2 halloc1
      have hfilled2 : filled_s base (k + 1) fill st2 := by
        simpa [st2] using (filled_s_updateVar base (k + 1) fill st1 "i" (.int (Int.ofNat (k + 1)))).2 hfilled1
      have hLoop2 :
          swhileWP rem memsetCond (memsetInv base n fill) memsetLoopBody
            (memsetLoopPost base n fill) st2 := by
        exact ih (k + 1) st2 hstep hdst2 hval2 hn2 hi2 halloc2 hfilled2
      have hEvalInc :
          evalExpr (.binop .add (.var "i") (.intLit 1)) st1 =
            some (.int (Int.ofNat (k + 1))) := by
        simpa [evalExpr, evalStaticExpr, hi1] using
          (show evalBinOp .add (.int (Int.ofNat k)) (.int 1) =
              some (.int (Int.ofNat (k + 1))) by
            change some (CVal.int (Int.ofNat k + 1)) =
              some (CVal.int (Int.ofNat (k + 1)))
            simp)
      have hAssignI :
          swp (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
            (fun _ => swhileWP rem memsetCond (memsetInv base n fill) memsetLoopBody
              (memsetLoopPost base n fill)) st1 := by
        simpa [swp, hEvalInc, st2] using hLoop2
      have hAssignWrite :
          swp (.assign (.deref (.binop .add (.var "dst") (.var "i"))) (.var "value"))
            (fun _ => swp (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
              (fun _ => swhileWP rem memsetCond (memsetInv base n fill) memsetLoopBody
                (memsetLoopPost base n fill))) st := by
        unfold swp
        simp [hEvalPtr, hEvalWrite]
        refine And.intro ?_ ?_
        · exact ⟨old, hReadPtr⟩
        · exact ⟨st1, hWritePtr, by simpa using hAssignI⟩
      have hBody :
          swp memsetLoopBody
            (fun _ => swhileWP rem memsetCond (memsetInv base n fill) memsetLoopBody
              (memsetLoopPost base n fill)) st := by
        simpa [memsetLoopBody, swp] using hAssignWrite
      simpa [swhileWP, hCond] using And.intro hInv hBody

theorem memset_correct (base n : Nat) (fill : Int) :
    ∀ st,
      st.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) →
      st.lookupVar "value" = some (.int fill) →
      st.lookupVar "n" = some (.int (Int.ofNat n)) →
      allocated_s base n st →
      ∃ st',
        execStmt (swhileFuel memsetLoopBody n + 2) memsetBody st =
          some (.returned (CVal.ptrAddr (base : PtrVal)) st') ∧
        filled_s base n fill st' := by
  intro st hdst hval hn halloc
  let st1 := st.updateVar "i" (.int 0)
  have hdst1 : st1.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) := by
    calc
      st1.lookupVar "dst" = st.lookupVar "dst" := by
        simpa [st1] using lookupVar_updateVar_ne st "i" "dst" (.int 0) (by decide : "dst" ≠ "i")
      _ = some (CVal.ptrAddr (base : PtrVal)) := hdst
  have hval1 : st1.lookupVar "value" = some (.int fill) := by
    calc
      st1.lookupVar "value" = st.lookupVar "value" := by
        simpa [st1] using lookupVar_updateVar_ne st "i" "value" (.int 0) (by decide : "value" ≠ "i")
      _ = some (.int fill) := hval
  have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat n)) := by
    calc
      st1.lookupVar "n" = st.lookupVar "n" := by
        simpa [st1] using lookupVar_updateVar_ne st "i" "n" (.int 0) (by decide : "n" ≠ "i")
      _ = some (.int (Int.ofNat n)) := hn
  have hi1 : st1.lookupVar "i" = some (.int 0) := by
    simpa [st1] using lookupVar_updateVar_eq st "i" (.int 0)
  have halloc1 : allocated_s base n st1 := by
    simpa [st1] using (allocated_s_updateVar base n st "i" (.int 0)).2 halloc
  have hfilled1 : filled_s base 0 fill st1 := by
    intro i hi
    omega
  have hLoopWP :
      swhileWP n memsetCond (memsetInv base n fill) memsetLoopBody
        (memsetLoopPost base n fill) st1 := by
    exact memset_loop_from_state base n fill n 0 st1 (by simp) hdst1 hval1 hn1 hi1 halloc1 hfilled1
  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel memsetLoopBody n)
          (.whileInv memsetCond HProp.htrue memsetLoopBody) st1 =
            some (.normal stLoop) ∧
        memsetLoopPost base n fill CVal.undef stLoop := by
    exact swhileWP_sound memsetCond (memsetInv base n fill) HProp.htrue memsetLoopBody
      memset_loopFree memset_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨hdstLoop, hiLoop, hfilledLoop⟩
  have hRet :
      execStmt (swhileFuel memsetLoopBody n) (.ret (.var "dst")) stLoop =
        some (.returned (CVal.ptrAddr (base : PtrVal)) stLoop) := by
    change execStmt (Nat.succ (stmtDepth memsetLoopBody + n)) (.ret (.var "dst")) stLoop =
      some (.returned (CVal.ptrAddr (base : PtrVal)) stLoop)
    simp [execStmt, hdstLoop]
  let loopFuel := swhileFuel memsetLoopBody n
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv memsetCond HProp.htrue memsetLoopBody) (.ret (.var "dst"))) st1 =
          some (.returned (CVal.ptrAddr (base : PtrVal)) stLoop) := by
    simp [execStmt]
    rw [hExecLoop]
    simpa [hRet]
  refine ⟨stLoop, ?_, hfilledLoop⟩
  change execStmt (Nat.succ (loopFuel + 1)) memsetBody st =
    some (.returned (CVal.ptrAddr (base : PtrVal)) stLoop)
  simpa [memsetBody, execStmt, st1] using hExecInner

end HeytingLean.LeanCP.RealWorld
