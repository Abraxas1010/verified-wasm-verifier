import HeytingLean.LeanCP.Examples.Swap
import HeytingLean.LeanCP.VCG.SWPSound

/-!
# LeanCP Example: Verified Swap

This is the first end-to-end discharged state-sensitive LeanCP verification
condition. The proof is relational in the initial addresses and values: the
same `addrA`, `addrB`, `va`, and `vb` from the precondition appear in the
postcondition in swapped positions.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

private theorem heap_read_write_eq (h : Heap) (addr : Nat) (v : CVal) :
    (h.write addr v).read addr = some v := by
  simp [Heap.read, Heap.write, Finmap.lookup_insert]

private theorem heap_read_write_ne (h : Heap) (addr addr' : Nat) (v : CVal)
    (hneq : addr' ≠ addr) :
    (h.write addr v).read addr' = h.read addr' := by
  simp [Heap.read, Heap.write, Finmap.lookup_insert_of_ne, hneq]

private theorem lookup_updateVarEnv_ne
    (env : Env) (x y : String) (v : CVal) (hxy : y ≠ x) :
    List.lookup y ((x, v) :: env.filter (fun p => p.1 != x)) = List.lookup y env := by
  induction env with
  | nil =>
      cases hyx : (y == x) with
      | true =>
          have : y = x := by simpa [beq_iff_eq] using hyx
          exact (hxy this).elim
      | false =>
          simp [List.lookup, hyx]
  | cons head tail ih =>
      rcases head with ⟨key, val⟩
      cases hyk : (y == key) with
      | true =>
          have : y = key := by simpa [beq_iff_eq] using hyk
          subst key
          cases hyx : (y == x) with
          | true =>
              have : y = x := by simpa [beq_iff_eq] using hyx
              exact (hxy this).elim
          | false =>
              have hkeep : (y != x) = true := by
                simpa [bne_iff_ne] using hxy
              simp [List.lookup, List.filter, hyx, hkeep]
      | false =>
          cases hkx : (key == x) with
          | true =>
              have : key = x := by simpa [beq_iff_eq] using hkx
              subst key
              cases hyx : (y == x) with
              | true =>
                  have : y = x := by simpa [beq_iff_eq] using hyx
                  exact (hxy this).elim
              | false =>
                  simpa [List.lookup, List.filter, hyk, hyx] using ih
          | false =>
              have hkxNe : key ≠ x := by
                simpa [beq_iff_eq] using hkx
              have hkeep : (key != x) = true := by
                simpa [bne_iff_ne] using hkxNe
              simpa [List.lookup, List.filter, hyk, hkeep] using ih

private theorem lookupVar_updateVar_eq (st : CState) (x : String) (v : CVal) :
    (st.updateVar x v).lookupVar x = some v := by
  simp [CState.lookupVar, CState.updateVar]

private theorem lookupVar_updateVar_ne (st : CState) (x y : String) (v : CVal)
    (hxy : y ≠ x) :
    (st.updateVar x v).lookupVar y = st.lookupVar y := by
  simpa [CState.lookupVar, CState.updateVar] using
    lookup_updateVarEnv_ne st.env x y v hxy

private theorem swap_loopFree : LoopFree swapBody := by
  simp [swapBody, LoopFree]

private theorem swap_tailReturn : TailReturn swapBody := by
  simp [swapBody, TailReturn, NoReturn]

/-- State-sensitive swap spec with fixed initial addresses and values. -/
def swapSSpec (addrA addrB : Nat) (va vb : CVal) : SFunSpec where
  name := "swap_state_sensitive"
  params := [("a", .ptr .int), ("b", .ptr .int)]
  retType := .void
  pre := fun st =>
    st.lookupVar "a" = some (CVal.ptrAddr (addrA : PtrVal)) ∧
    st.lookupVar "b" = some (CVal.ptrAddr (addrB : PtrVal)) ∧
    st.heap.read addrA = some va ∧
    st.heap.read addrB = some vb ∧
    addrA ≠ addrB
  post := fun _ st =>
    st.lookupVar "a" = some (CVal.ptrAddr (addrA : PtrVal)) ∧
    st.lookupVar "b" = some (CVal.ptrAddr (addrB : PtrVal)) ∧
    st.heap.read addrA = some vb ∧
    st.heap.read addrB = some va
  body := swapBody

theorem swap_verified (addrA addrB : Nat) (va vb : CVal) :
    sgenVC (swapSSpec addrA addrB va vb) := by
  intro st hpre
  rcases hpre with ⟨hVarA, hVarB, hreadA, hreadB, hab⟩
  have hReadPtrA : st.readPtr addrA = some va := by
    simpa [hreadA] using (CState.readPtr_block0 st addrA addrA)

  have hEvalA : evalExpr (.deref (.var "a")) st = some va := by
    simpa [evalExpr, evalStaticExpr, hVarA] using hReadPtrA

  let st1 := st.updateVar "tmp" va

  have ha1 : st1.lookupVar "a" = some (CVal.ptrAddr (addrA : PtrVal)) := by
    calc
      st1.lookupVar "a" = st.lookupVar "a" := by
        simpa [st1] using lookupVar_updateVar_ne st "tmp" "a" va (by decide : "a" ≠ "tmp")
      _ = some (CVal.ptrAddr (addrA : PtrVal)) := hVarA
  have hb1 : st1.lookupVar "b" = some (CVal.ptrAddr (addrB : PtrVal)) := by
    calc
      st1.lookupVar "b" = st.lookupVar "b" := by
        simpa [st1] using lookupVar_updateVar_ne st "tmp" "b" va (by decide : "b" ≠ "tmp")
      _ = some (CVal.ptrAddr (addrB : PtrVal)) := hVarB
  have htmp1 : st1.lookupVar "tmp" = some va := by
    simpa [st1] using lookupVar_updateVar_eq st "tmp" va
  have hreadA1 : st1.heap.read addrA = some va := by
    simpa [st1]
  have hreadB1 : st1.heap.read addrB = some vb := by
    simpa [st1]
  have hReadPtrA1 : st1.readPtr addrA = some va := by
    simpa [hreadA1] using (CState.readPtr_block0 st1 addrA addrA)
  have hReadPtrB1 : st1.readPtr addrB = some vb := by
    simpa [hreadB1] using (CState.readPtr_block0 st1 addrB addrB)
  have hEvalB1 : evalExpr (.deref (.var "b")) st1 = some vb := by
    simpa [evalExpr, hb1] using hReadPtrB1
  have hEvalVarA1 : evalExpr (.var "a") st1 = some (CVal.ptrAddr (addrA : PtrVal)) := by
    simpa [evalExpr] using ha1

  let st2 : CState := st1.withHeap (st1.heap.write addrA vb)

  have hreadA2 : st2.heap.read addrA = some vb := by
    simpa [st2] using heap_read_write_eq st1.heap addrA vb
  have hreadB2 : st2.heap.read addrB = some vb := by
    calc
      st2.heap.read addrB = st1.heap.read addrB := by
        simpa [st2] using heap_read_write_ne st1.heap addrA addrB vb hab.symm
      _ = some vb := hreadB1
  have ha2 : st2.lookupVar "a" = some (CVal.ptrAddr (addrA : PtrVal)) := by
    exact ha1
  have hb2 : st2.lookupVar "b" = some (CVal.ptrAddr (addrB : PtrVal)) := by
    exact hb1
  have htmp2 : st2.lookupVar "tmp" = some va := by
    exact htmp1
  have hEvalTmp2 : evalExpr (.var "tmp") st2 = some va := by
    simpa [evalExpr] using htmp2
  have hEvalVarB2 : evalExpr (.var "b") st2 = some (CVal.ptrAddr (addrB : PtrVal)) := by
    simpa [evalExpr] using hb2
  have hReadPtrB2 : st2.readPtr addrB = some vb := by
    simpa [hreadB2] using (CState.readPtr_block0 st2 addrB addrB)

  let st3 : CState := st2.withHeap (st2.heap.write addrB va)
  have hWritePtrA1 : st1.writePtr addrA vb = some st2 := by
    simpa [st2] using (CState.writePtr_block0 st1 addrA addrA vb)
  have hWritePtrB2 : st2.writePtr addrB va = some st3 := by
    simpa [st3] using (CState.writePtr_block0 st2 addrB addrB va)

  have hpost : (swapSSpec addrA addrB va vb).post CVal.undef st3 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ha2
    · exact hb2
    · calc
        st3.heap.read addrA = st2.heap.read addrA := by
          simpa [st3] using heap_read_write_ne st2.heap addrB addrA va hab
        _ = some vb := hreadA2
    · simpa [swapSSpec, st3] using heap_read_write_eq st2.heap addrB va

  change swp (.seq (.assign (.var "tmp") (.deref (.var "a")))
      (.seq (.assign (.deref (.var "a")) (.deref (.var "b")))
        (.assign (.deref (.var "b")) (.var "tmp"))))
      (swapSSpec addrA addrB va vb).post st
  simp [swp, hEvalA]
  have hpairB :
      (∃ vOld, st2.readPtr addrB = some vOld) ∧
        ∃ st', st2.writePtr addrB va = some st' ∧ (swapSSpec addrA addrB va vb).post CVal.undef st' := by
    exact ⟨⟨vb, hReadPtrB2⟩, ⟨st3, hWritePtrB2, hpost⟩⟩
  have hthird :
      swp (.assign (.deref (.var "b")) (.var "tmp"))
        (swapSSpec addrA addrB va vb).post st2 := by
    simpa [swp, hEvalVarB2, hEvalTmp2, st2, st3] using hpairB
  have hpairA :
      (∃ vOld, st1.readPtr addrA = some vOld) ∧
        ∃ st', st1.writePtr addrA vb = some st' ∧
          swp (.assign (.deref (.var "b")) (.var "tmp"))
            (swapSSpec addrA addrB va vb).post st' := by
    exact ⟨⟨va, hReadPtrA1⟩, ⟨st2, hWritePtrA1, hthird⟩⟩
  simpa [swp, hEvalVarA1, hEvalB1, st1, st2] using
    hpairA

theorem swap_executes (addrA addrB : Nat) (va vb : CVal) {st fuel}
    (hpre : (swapSSpec addrA addrB va vb).pre st)
    (hfuel : stmtDepth swapBody ≤ fuel) :
    ∃ res, execStmt fuel swapBody st = some res ∧
      match res with
      | .returned v st' => (swapSSpec addrA addrB va vb).post v st'
      | .normal st' => (swapSSpec addrA addrB va vb).post CVal.undef st' := by
  have hvc : swp swapBody (swapSSpec addrA addrB va vb).post st :=
    swap_verified addrA addrB va vb st hpre
  exact swp_sound swapBody swap_loopFree swap_tailReturn hfuel hvc

end HeytingLean.LeanCP.Examples
