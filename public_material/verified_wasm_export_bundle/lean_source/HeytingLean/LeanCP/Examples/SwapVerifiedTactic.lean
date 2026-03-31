import HeytingLean.LeanCP.Examples.SwapVerified
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

attribute [leancp_unfold] swapBody

theorem swap_verified_tactic (addrA addrB : Nat) (va vb : CVal) :
    sgenVC (swapSSpec addrA addrB va vb) := by
  intro st hpre
  rcases hpre with ⟨hVarA, hVarB, hreadA, hreadB, hab⟩
  have hbTmp : "b" ≠ "tmp" := by decide
  have haTmp : "a" ≠ "tmp" := by decide
  have hReadPtrA : st.readPtr addrA = some va := by
    simpa [hreadA] using (CState.readPtr_block0 st addrA addrA)
  have hEvalA : evalExpr (.deref (.var "a")) st = some va := by
    simpa [evalExpr, evalStaticExpr, hVarA] using hReadPtrA
  let st1 := st.updateVar "tmp" va
  have hreadA1 : st1.heap.read addrA = some va := by
    simpa [st1]
  have hreadB1 : st1.heap.read addrB = some vb := by
    simpa [st1]
  have hReadPtrA1 : st1.readPtr addrA = some va := by
    simpa [hreadA1] using (CState.readPtr_block0 st1 addrA addrA)
  have hReadPtrB1 : st1.readPtr addrB = some vb := by
    simpa [hreadB1] using (CState.readPtr_block0 st1 addrB addrB)
  have hEvalB1 : evalExpr (.deref (.var "b")) st1 = some vb := by
    have hb1 : st1.lookupVar "b" = some (CVal.ptrAddr (addrB : PtrVal)) := by
      calc
        st1.lookupVar "b" = st.lookupVar "b" := by
          simpa [st1] using lookupVar_updateVar_ne st "tmp" "b" va hbTmp
        _ = some (CVal.ptrAddr (addrB : PtrVal)) := hVarB
    simpa [evalExpr, evalStaticExpr, hb1] using hReadPtrB1
  have hEvalVarA1 : evalExpr (.var "a") st1 = some (CVal.ptrAddr (addrA : PtrVal)) := by
    have ha1 : st1.lookupVar "a" = some (CVal.ptrAddr (addrA : PtrVal)) := by
      calc
        st1.lookupVar "a" = st.lookupVar "a" := by
          simpa [st1] using lookupVar_updateVar_ne st "tmp" "a" va haTmp
        _ = some (CVal.ptrAddr (addrA : PtrVal)) := hVarA
    simpa [evalExpr] using ha1
  let st2 : CState := st1.withHeap (st1.heap.write addrA vb)
  have hreadB2 : st2.heap.read addrB = some vb := by
    calc
      st2.heap.read addrB = st1.heap.read addrB := by
        simpa [st2] using heap_read_write_ne st1.heap addrA addrB vb hab.symm
      _ = some vb := hreadB1
  have hWritePtrA1 : st1.writePtr addrA vb = some st2 := by
    simpa [st2] using (CState.writePtr_block0 st1 addrA addrA vb)
  have hEvalVarB2 : evalExpr (.var "b") st2 = some (CVal.ptrAddr (addrB : PtrVal)) := by
    have hb2 : st2.lookupVar "b" = some (CVal.ptrAddr (addrB : PtrVal)) := by
      calc
        st2.lookupVar "b" = st1.lookupVar "b" := rfl
        _ = st.lookupVar "b" := by
          simpa [st1] using lookupVar_updateVar_ne st "tmp" "b" va hbTmp
        _ = some (CVal.ptrAddr (addrB : PtrVal)) := hVarB
    simpa [evalExpr] using hb2
  have hEvalTmp2 : evalExpr (.var "tmp") st2 = some va := by
    have htmp2 : st2.lookupVar "tmp" = some va := by
      calc
        st2.lookupVar "tmp" = st1.lookupVar "tmp" := rfl
        _ = some va := by
          simpa [st1] using lookupVar_updateVar_eq st "tmp" va
    simpa [evalExpr] using htmp2
  have hReadPtrB2 : st2.readPtr addrB = some vb := by
    simpa [hreadB2] using (CState.readPtr_block0 st2 addrB addrB)
  let st3 : CState := st2.withHeap (st2.heap.write addrB va)
  have hWritePtrB2 : st2.writePtr addrB va = some st3 := by
    simpa [st3] using (CState.writePtr_block0 st2 addrB addrB va)
  have hpost : (swapSSpec addrA addrB va vb).post CVal.undef st3 := by
    have ha3 : st3.lookupVar "a" = some (CVal.ptrAddr (addrA : PtrVal)) := by
      calc
        st3.lookupVar "a" = st2.lookupVar "a" := rfl
        _ = st1.lookupVar "a" := rfl
        _ = st.lookupVar "a" := by
          simpa [st1] using lookupVar_updateVar_ne st "tmp" "a" va haTmp
        _ = some (CVal.ptrAddr (addrA : PtrVal)) := hVarA
    have hb3 : st3.lookupVar "b" = some (CVal.ptrAddr (addrB : PtrVal)) := by
      calc
        st3.lookupVar "b" = st2.lookupVar "b" := rfl
        _ = st1.lookupVar "b" := rfl
        _ = st.lookupVar "b" := by
          simpa [st1] using lookupVar_updateVar_ne st "tmp" "b" va hbTmp
        _ = some (CVal.ptrAddr (addrB : PtrVal)) := hVarB
    refine ⟨ha3, hb3, ?_, ?_⟩
    · calc
        st3.heap.read addrA = st2.heap.read addrA := by
          simpa [st3] using heap_read_write_ne st2.heap addrB addrA va hab
        _ = some vb := by
          simpa [st2] using heap_read_write_eq st1.heap addrA vb
    · simpa [st3] using heap_read_write_eq st2.heap addrB va
  change swp swapBody (swapSSpec addrA addrB va vb).post st
  have hThird :
      swp (.assign (.deref (.var "b")) (.var "tmp"))
        (swapSSpec addrA addrB va vb).post st2 := by
    simpa [swp, hEvalVarB2, hEvalTmp2, st2, st3] using
      (show (∃ vOld, st2.readPtr addrB = some vOld) ∧
          ∃ st', st2.writePtr addrB va = some st' ∧
            (swapSSpec addrA addrB va vb).post CVal.undef st' from
        ⟨⟨vb, hReadPtrB2⟩, ⟨st3, hWritePtrB2, hpost⟩⟩)
  have hSecond :
      swp (.seq (.assign (.deref (.var "a")) (.deref (.var "b")))
          (.assign (.deref (.var "b")) (.var "tmp")))
        (swapSSpec addrA addrB va vb).post st1 := by
    simpa [swp, hEvalVarA1, hEvalB1, st2] using
      (show (∃ vOld, st1.readPtr addrA = some vOld) ∧
          ∃ st', st1.writePtr addrA vb = some st' ∧
            swp (.assign (.deref (.var "b")) (.var "tmp"))
              (swapSSpec addrA addrB va vb).post st' from
        ⟨⟨va, hReadPtrA1⟩, ⟨st2, hWritePtrA1, hThird⟩⟩)
  simpa [swapBody, swp, hEvalA, st1] using hSecond

end HeytingLean.LeanCP.Examples
