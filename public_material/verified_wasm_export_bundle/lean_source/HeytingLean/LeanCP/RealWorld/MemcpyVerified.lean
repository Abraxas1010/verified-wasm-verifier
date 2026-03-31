import HeytingLean.LeanCP.RealWorld.Support
import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.VarLemmas
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

def memcpyCond : CExpr :=
  .binop .lt (.var "i") (.var "n")

def memcpyLoopBody : CStmt :=
  .seq
    (.assign (.deref (.binop .add (.var "dst") (.var "i")))
      (.deref (.binop .add (.var "src") (.var "i"))))
    (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))

def memcpyBody : CStmt :=
  .seq (.assign (.var "i") (.intLit 0))
    (.seq (.whileInv memcpyCond HProp.htrue memcpyLoopBody)
      (.ret (.var "dst")))

def memcpyInv (dstBase srcBase : Nat) (vals : List Int) : SProp := fun st =>
  ∃ k,
    k ≤ vals.length ∧
    st.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) ∧
    st.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) ∧
    st.lookupVar "n" = some (.int (Int.ofNat vals.length)) ∧
    st.lookupVar "i" = some (.int (Int.ofNat k)) ∧
    allocated_s dstBase vals.length st ∧
    bytesAt_s srcBase vals st ∧
    copiedPrefix_s dstBase srcBase k st

def memcpyLoopPost (dstBase srcBase : Nat) (vals : List Int) : CVal → SProp := fun _ st =>
  st.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) ∧
  st.lookupVar "i" = some (.int (Int.ofNat vals.length)) ∧
  bytesAt_s srcBase vals st ∧
  copiedPrefix_s dstBase srcBase vals.length st

private theorem memcpy_loopFree : LoopFree memcpyLoopBody := by
  simp [memcpyLoopBody, LoopFree]

private theorem memcpy_noReturn : NoReturn memcpyLoopBody := by
  simp [memcpyLoopBody, NoReturn]

private theorem memcpy_loop_from_state
    (dstBase srcBase : Nat) (vals : List Int)
    (hdisj : disjointRanges dstBase vals.length srcBase vals.length) :
    ∀ rem k st,
      vals.length = k + rem →
      st.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) →
      st.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) →
      st.lookupVar "n" = some (.int (Int.ofNat vals.length)) →
      st.lookupVar "i" = some (.int (Int.ofNat k)) →
      allocated_s dstBase vals.length st →
      bytesAt_s srcBase vals st →
      copiedPrefix_s dstBase srcBase k st →
      swhileWP rem memcpyCond (memcpyInv dstBase srcBase vals) memcpyLoopBody
        (memcpyLoopPost dstBase srcBase vals) st := by
  intro rem
  induction rem with
  | zero =>
      intro k st hk hdst hsrc hn hi halloc hsrcBytes hcopy
      have hkEq : k = vals.length := by omega
      have hInv : memcpyInv dstBase srcBase vals st := by
        refine ⟨k, ?_, hdst, hsrc, hn, hi, halloc, hsrcBytes, hcopy⟩
        omega
      have hCond : evalExpr memcpyCond st = some (.int 0) := by
        simpa [memcpyCond, evalExpr, evalStaticExpr, hi, hn, hkEq] using
          (show evalBinOp .lt (.int (Int.ofNat vals.length)) (.int (Int.ofNat vals.length)) =
              some (.int 0) by
            change some (CVal.int (if Int.ofNat vals.length < Int.ofNat vals.length then 1 else 0)) =
              some (CVal.int 0)
            simp)
      have hPost : memcpyLoopPost dstBase srcBase vals CVal.undef st := by
        refine ⟨hdst, ?_, hsrcBytes, ?_⟩
        simpa [hkEq] using hi
        simpa [hkEq] using hcopy
      simpa [swhileWP, hCond, isTruthy] using And.intro hInv hPost
  | succ rem ih =>
      intro k st hk hdst hsrc hn hi halloc hsrcBytes hcopy
      have hklt : k < vals.length := by omega
      have hInv : memcpyInv dstBase srcBase vals st := by
        refine ⟨k, ?_, hdst, hsrc, hn, hi, halloc, hsrcBytes, hcopy⟩
        omega
      have hltInt : Int.ofNat k < Int.ofNat vals.length := Int.ofNat_lt.mpr hklt
      have hBin :
          evalBinOp .lt (.int (Int.ofNat k)) (.int (Int.ofNat vals.length)) =
            some (.int 1) := by
        change some (CVal.int (if Int.ofNat k < Int.ofNat vals.length then 1 else 0)) =
          some (CVal.int 1)
        rw [if_pos hltInt]
      have hCond : evalExpr memcpyCond st = some (.int 1) := by
        simpa [memcpyCond, evalExpr, evalStaticExpr, hi, hn] using hBin
      have hEvalDstPtr :
          evalExpr (.binop .add (.var "dst") (.var "i")) st =
            some (CVal.ptrAddr ((dstBase + k) : PtrVal)) := by
        simpa [evalExpr, evalStaticExpr, hdst, hi] using
          (show evalBinOp .add (CVal.ptrAddr (dstBase : PtrVal)) (.int (Int.ofNat k)) =
              some (CVal.ptrAddr ((dstBase + k) : PtrVal)) by
            change
              (if 0 ≤ Int.ofNat k then
                some (CVal.ptrAddr { block := 0, offset := Int.ofNat dstBase + Int.ofNat k })
              else none) = some (CVal.ptrAddr ((dstBase + k) : PtrVal))
            simp)
      have hEvalSrcPtr :
          evalExpr (.binop .add (.var "src") (.var "i")) st =
            some (CVal.ptrAddr ((srcBase + k) : PtrVal)) := by
        simpa [evalExpr, evalStaticExpr, hsrc, hi] using
          (show evalBinOp .add (CVal.ptrAddr (srcBase : PtrVal)) (.int (Int.ofNat k)) =
              some (CVal.ptrAddr ((srcBase + k) : PtrVal)) by
            change
              (if 0 ≤ Int.ofNat k then
                some (CVal.ptrAddr { block := 0, offset := Int.ofNat srcBase + Int.ofNat k })
              else none) = some (CVal.ptrAddr ((srcBase + k) : PtrVal))
            simp)
      have hReadSrc : st.heap.read (srcBase + k) = some (.int vals[k]) := by
        exact hsrcBytes k vals[k] (by simpa [List.getElem?_eq_getElem hklt])
      have hReadPtrSrc : st.readPtr ((srcBase + k) : PtrVal) = some (.int vals[k]) := by
        simpa [hReadSrc] using CState.readPtr_block0 st (srcBase + k) (srcBase + k)
      have hEvalRead :
          evalExpr (.deref (.binop .add (.var "src") (.var "i"))) st = some (.int vals[k]) := by
        simpa [evalExpr, evalStaticExpr, hEvalSrcPtr] using hReadPtrSrc
      rcases halloc k hklt with ⟨old, hold⟩
      have hReadPtrDst : st.readPtr ((dstBase + k) : PtrVal) = some old := by
        simpa [hold] using CState.readPtr_block0 st (dstBase + k) (dstBase + k)
      let st1 : CState := st.withHeap (st.heap.write (dstBase + k) (.int vals[k]))
      have hWritePtr :
          st.writePtr ((dstBase + k) : PtrVal) (.int vals[k]) = some st1 := by
        simpa [st1] using CState.writePtr_block0 st (dstBase + k) (dstBase + k) (.int vals[k])
      have hdst1 : st1.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) := by
        simpa [st1, CState.lookupVar, CState.withHeap] using hdst
      have hsrc1Var : st1.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) := by
        simpa [st1, CState.lookupVar, CState.withHeap] using hsrc
      have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
        simpa [st1, CState.lookupVar, CState.withHeap] using hn
      have hi1 : st1.lookupVar "i" = some (.int (Int.ofNat k)) := by
        simpa [st1, CState.lookupVar, CState.withHeap] using hi
      have halloc1 : allocated_s dstBase vals.length st1 := by
        exact allocated_s_write_preserved st dstBase vals.length (dstBase + k) (.int vals[k]) halloc
      have hsrcBytes1 : bytesAt_s srcBase vals st1 := by
        intro i v hv
        have hi' : i < vals.length := (List.getElem?_eq_some_iff.mp hv).1
        calc
          st1.heap.read (srcBase + i) = (st.heap.write (dstBase + k) (.int vals[k])).read (srcBase + i) := by
            simp [st1]
          _ = st.heap.read (srcBase + i) := by
                apply heap_read_write_ne
                exact (disjointRanges_index_ne hdisj hklt hi').symm
          _ = some (.int v) := hsrcBytes i v hv
      have hcopy1 : copiedPrefix_s dstBase srcBase (k + 1) st1 := by
        apply copiedPrefix_s_succ_of_write st dstBase srcBase k vals[k] hcopy hReadSrc
        intro i hi'
        have hiVals : i < vals.length := by omega
        exact disjointRanges_index_ne hdisj hklt hiVals
      let st2 := st1.updateVar "i" (.int (Int.ofNat (k + 1)))
      have hstep : vals.length = (k + 1) + rem := by omega
      have hdst2 : st2.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) := by
        calc
          st2.lookupVar "dst" = st1.lookupVar "dst" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "i" "dst" (.int (Int.ofNat (k + 1)))
              (by decide : "dst" ≠ "i")
          _ = some (CVal.ptrAddr (dstBase : PtrVal)) := hdst1
      have hsrc2 : st2.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) := by
        calc
          st2.lookupVar "src" = st1.lookupVar "src" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "i" "src" (.int (Int.ofNat (k + 1)))
              (by decide : "src" ≠ "i")
          _ = some (CVal.ptrAddr (srcBase : PtrVal)) := hsrc1Var
      have hn2 : st2.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
        calc
          st2.lookupVar "n" = st1.lookupVar "n" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "i" "n" (.int (Int.ofNat (k + 1)))
              (by decide : "n" ≠ "i")
          _ = some (.int (Int.ofNat vals.length)) := hn1
      have hi2 : st2.lookupVar "i" = some (.int (Int.ofNat (k + 1))) := by
        simpa [st2] using lookupVar_updateVar_eq st1 "i" (.int (Int.ofNat (k + 1)))
      have halloc2 : allocated_s dstBase vals.length st2 := by
        simpa [st2] using (allocated_s_updateVar dstBase vals.length st1 "i" (.int (Int.ofNat (k + 1)))).2 halloc1
      have hsrcBytes2 : bytesAt_s srcBase vals st2 := by
        simpa [st2] using (bytesAt_s_updateVar srcBase vals st1 "i" (.int (Int.ofNat (k + 1)))).2 hsrcBytes1
      have hcopy2 : copiedPrefix_s dstBase srcBase (k + 1) st2 := by
        simpa [st2] using (copiedPrefix_s_updateVar dstBase srcBase (k + 1) st1 "i" (.int (Int.ofNat (k + 1)))).2 hcopy1
      have hLoop2 :
          swhileWP rem memcpyCond (memcpyInv dstBase srcBase vals) memcpyLoopBody
            (memcpyLoopPost dstBase srcBase vals) st2 := by
        exact ih (k + 1) st2 hstep hdst2 hsrc2 hn2 hi2 halloc2 hsrcBytes2 hcopy2
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
            (fun _ => swhileWP rem memcpyCond (memcpyInv dstBase srcBase vals) memcpyLoopBody
              (memcpyLoopPost dstBase srcBase vals)) st1 := by
        simpa [swp, hEvalInc, st2] using hLoop2
      have hAssignWrite :
          swp (.assign (.deref (.binop .add (.var "dst") (.var "i")))
                (.deref (.binop .add (.var "src") (.var "i"))))
            (fun _ => swp (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
              (fun _ => swhileWP rem memcpyCond (memcpyInv dstBase srcBase vals) memcpyLoopBody
                (memcpyLoopPost dstBase srcBase vals))) st := by
        unfold swp
        simp [hEvalDstPtr, hEvalRead]
        refine And.intro ?_ ?_
        · exact ⟨old, hReadPtrDst⟩
        · exact ⟨st1, hWritePtr, by simpa using hAssignI⟩
      have hBody :
          swp memcpyLoopBody
            (fun _ => swhileWP rem memcpyCond (memcpyInv dstBase srcBase vals) memcpyLoopBody
              (memcpyLoopPost dstBase srcBase vals)) st := by
        simpa [memcpyLoopBody, swp] using hAssignWrite
      simpa [swhileWP, hCond] using And.intro hInv hBody

theorem memcpy_correct (dstBase srcBase : Nat) (vals : List Int)
    (hdisj : disjointRanges dstBase vals.length srcBase vals.length) :
    ∀ st,
      st.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) →
      st.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) →
      st.lookupVar "n" = some (.int (Int.ofNat vals.length)) →
      allocated_s dstBase vals.length st →
      bytesAt_s srcBase vals st →
      ∃ st',
        execStmt (swhileFuel memcpyLoopBody vals.length + 2) memcpyBody st =
          some (.returned (CVal.ptrAddr (dstBase : PtrVal)) st') ∧
        bytesAt_s srcBase vals st' ∧
        bytesAt_s dstBase vals st' := by
  intro st hdst hsrc hn halloc hsrcBytes
  let st1 := st.updateVar "i" (.int 0)
  have hdst1 : st1.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) := by
    calc
      st1.lookupVar "dst" = st.lookupVar "dst" := by
        simpa [st1] using lookupVar_updateVar_ne st "i" "dst" (.int 0) (by decide : "dst" ≠ "i")
      _ = some (CVal.ptrAddr (dstBase : PtrVal)) := hdst
  have hsrc1 : st1.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) := by
    calc
      st1.lookupVar "src" = st.lookupVar "src" := by
        simpa [st1] using lookupVar_updateVar_ne st "i" "src" (.int 0) (by decide : "src" ≠ "i")
      _ = some (CVal.ptrAddr (srcBase : PtrVal)) := hsrc
  have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
    calc
      st1.lookupVar "n" = st.lookupVar "n" := by
        simpa [st1] using lookupVar_updateVar_ne st "i" "n" (.int 0) (by decide : "n" ≠ "i")
      _ = some (.int (Int.ofNat vals.length)) := hn
  have hi1 : st1.lookupVar "i" = some (.int 0) := by
    simpa [st1] using lookupVar_updateVar_eq st "i" (.int 0)
  have halloc1 : allocated_s dstBase vals.length st1 := by
    simpa [st1] using (allocated_s_updateVar dstBase vals.length st "i" (.int 0)).2 halloc
  have hsrcBytes1 : bytesAt_s srcBase vals st1 := by
    simpa [st1] using (bytesAt_s_updateVar srcBase vals st "i" (.int 0)).2 hsrcBytes
  have hcopy1 : copiedPrefix_s dstBase srcBase 0 st1 := by
    intro i hi
    omega
  have hLoopWP :
      swhileWP vals.length memcpyCond (memcpyInv dstBase srcBase vals) memcpyLoopBody
        (memcpyLoopPost dstBase srcBase vals) st1 := by
    exact memcpy_loop_from_state dstBase srcBase vals hdisj vals.length 0 st1 (by simp)
      hdst1 hsrc1 hn1 hi1 halloc1 hsrcBytes1 hcopy1
  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel memcpyLoopBody vals.length)
          (.whileInv memcpyCond HProp.htrue memcpyLoopBody) st1 =
            some (.normal stLoop) ∧
        memcpyLoopPost dstBase srcBase vals CVal.undef stLoop := by
    exact swhileWP_sound memcpyCond (memcpyInv dstBase srcBase vals) HProp.htrue memcpyLoopBody
      memcpy_loopFree memcpy_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨hdstLoop, hiLoop, hsrcLoop, hcopyLoop⟩
  have hdstBytes : bytesAt_s dstBase vals stLoop := by
    intro i v hv
    have hi' : i < vals.length := (List.getElem?_eq_some_iff.mp hv).1
    have hsrcRead : stLoop.heap.read (srcBase + i) = some (.int v) := hsrcLoop i v hv
    calc
      stLoop.heap.read (dstBase + i) = stLoop.heap.read (srcBase + i) := hcopyLoop i hi'
      _ = some (.int v) := hsrcRead
  have hRet :
      execStmt (swhileFuel memcpyLoopBody vals.length) (.ret (.var "dst")) stLoop =
        some (.returned (CVal.ptrAddr (dstBase : PtrVal)) stLoop) := by
    change execStmt (Nat.succ (stmtDepth memcpyLoopBody + vals.length)) (.ret (.var "dst")) stLoop =
      some (.returned (CVal.ptrAddr (dstBase : PtrVal)) stLoop)
    simp [execStmt, hdstLoop]
  let loopFuel := swhileFuel memcpyLoopBody vals.length
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv memcpyCond HProp.htrue memcpyLoopBody) (.ret (.var "dst"))) st1 =
          some (.returned (CVal.ptrAddr (dstBase : PtrVal)) stLoop) := by
    simp [execStmt]
    rw [hExecLoop]
    simpa [hRet]
  refine ⟨stLoop, ?_, hsrcLoop, hdstBytes⟩
  change execStmt (Nat.succ (loopFuel + 1)) memcpyBody st =
    some (.returned (CVal.ptrAddr (dstBase : PtrVal)) stLoop)
  simpa [memcpyBody, execStmt, st1] using hExecInner

end HeytingLean.LeanCP.RealWorld
