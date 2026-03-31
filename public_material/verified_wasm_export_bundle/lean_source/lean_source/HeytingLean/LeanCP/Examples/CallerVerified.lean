import HeytingLean.LeanCP.VCG.SWPCallSound
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Tactics.Forward

/-!
# LeanCP Example: Operational Caller

This module exercises the new operational call semantics directly.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

private theorem bindCallEnv_single_p (ptr : PtrVal) :
    bindCallEnv [("p", .ptr .int)] [CVal.ptrAddr ptr] = [("p", CVal.ptrAddr ptr)] := by
  simp [bindCallEnv]

def incrementBody : CStmt :=
  .seq
    (.assign (.deref (.var "p")) (.binop .add (.deref (.var "p")) (.intLit 1)))
    (.ret (.deref (.var "p")))

def incrementSpec (addr : Nat) (n : Int) : SFunSpec where
  name := "increment"
  params := [("p", .ptr .int)]
  retType := .int
  pre := fun st =>
    st.lookupVar "p" = some (CVal.ptrAddr (addr : PtrVal)) ∧
    st.heap.read addr = some (.int n)
  post := fun ret st =>
    ret = .int (n + 1) ∧
    st.lookupVar "p" = some (CVal.ptrAddr (addr : PtrVal)) ∧
    st.heap.read addr = some (.int (n + 1))
  body := incrementBody

private theorem increment_entry_state (st : CState) (addr : Nat) (n : Int) :
    callEntryState st (incrementSpec addr n) [CVal.ptrAddr (addr : PtrVal)] =
      { heap := st.heap, env := [("p", CVal.ptrAddr (addr : PtrVal))], nextAddr := st.nextAddr,
        mem := st.mem, allocs := st.allocs } := by
  simp [callEntryState, incrementSpec, bindCallEnv_single_p]

private theorem increment_entry_lookup_p (st : CState) (addr : Nat) (n : Int) :
    (callEntryState st (incrementSpec addr n) [CVal.ptrAddr (addr : PtrVal)]).lookupVar "p" =
      some (CVal.ptrAddr (addr : PtrVal)) := by
  simp [callEntryState, incrementSpec, bindCallEnv_single_p, CState.lookupVar]

private theorem restoreCaller_after_increment (st : CState) (addr : Nat) (n : Int) :
    restoreCallerState st
        ((callEntryState st (incrementSpec addr n) [CVal.ptrAddr (addr : PtrVal)]).withHeap
          (st.heap.write addr (.int (n + 1)))) =
      st.withHeap (st.heap.write addr (.int (n + 1))) := by
  simp [callEntryState, incrementSpec, restoreCallerState, bindCallEnv_single_p, CState.withHeap]

def callerFunEnv (addr : Nat) (n : Int) : FunEnv
  | "increment" => some (incrementSpec addr n)
  | _ => none

def callerBody : CStmt :=
  .seq (.assign (.var "result") (.call "increment" [.var "p"]))
    (.ret (.var "result"))

def callerSpec (addr : Nat) (n : Int) : SFunSpec where
  name := "caller"
  params := [("p", .ptr .int)]
  retType := .int
  pre := fun st =>
    st.lookupVar "p" = some (CVal.ptrAddr (addr : PtrVal)) ∧
    st.heap.read addr = some (.int n)
  post := fun ret st =>
    ret = .int (n + 1) ∧
    st.lookupVar "p" = some (CVal.ptrAddr (addr : PtrVal)) ∧
    st.heap.read addr = some (.int (n + 1))
  body := callerBody

theorem increment_executes (addr : Nat) (n : Int) :
    ∀ st,
      (incrementSpec addr n).pre st →
      execStmt 2 incrementBody st =
        some (.returned (.int (n + 1)) (st.withHeap (st.heap.write addr (.int (n + 1))))) := by
  intro st hpre
  rcases hpre with ⟨hp, hheap⟩
  have hEvalP : evalExpr (.var "p") st = some (CVal.ptrAddr (addr : PtrVal)) := by
    simpa [evalExpr] using hp
  have hReadPtr : st.readPtr (addr : PtrVal) = some (.int n) := by
    simpa [hheap] using (CState.readPtr_block0 st addr addr)
  have hEvalDeref : evalExpr (.deref (.var "p")) st = some (.int n) := by
    simpa [evalExpr, evalStaticExpr, hEvalP] using hReadPtr
  have hStaticAdd :
      evalStaticExpr (.binop .add (.deref (.var "p")) (.intLit 1)) = none := by
    simp [evalStaticExpr]
  have hEvalOne : evalExpr (.intLit 1) st = some (.int 1) := by
    rfl
  have hEvalAdd :
      evalExpr (.binop .add (.deref (.var "p")) (.intLit 1)) st = some (.int (n + 1)) := by
    rw [evalExpr, hStaticAdd, hEvalDeref, hEvalOne]
    · rfl
    · intro h
      cases h
    · intro h
      cases h
  let st1 : CState := st.withHeap (st.heap.write addr (.int (n + 1)))
  have hWritePtr : st.writePtr (addr : PtrVal) (.int (n + 1)) = some st1 := by
    simpa [st1] using (CState.writePtr_block0 st addr addr (.int (n + 1)))
  have hp1 : st1.lookupVar "p" = some (CVal.ptrAddr (addr : PtrVal)) := by
    simpa [st1, CState.lookupVar] using hp
  have hEvalRet : evalExpr (.deref (.var "p")) st1 = some (.int (n + 1)) := by
    have hReadPtr1 : st1.readPtr (addr : PtrVal) = some (.int (n + 1)) := by
      calc
        st1.readPtr (addr : PtrVal) = st1.heap.read addr := by
          simpa using (CState.readPtr_block0 st1 addr addr)
        _ = some (.int (n + 1)) := by
          simpa [st1] using heap_read_write_eq st.heap addr (.int (n + 1))
    simpa [evalExpr, evalStaticExpr, hp1] using hReadPtr1
  simp [execStmt, incrementBody, hEvalP, hEvalAdd]
  change
    ((Option.map ExecResult.normal
        (st.writePtr (addr : PtrVal) (.int (n + 1)))).bind
        fun __do_lift =>
        match __do_lift with
        | ExecResult.normal st' =>
            (evalExpr (.deref (.var "p")) st').bind fun v => some (ExecResult.returned v st')
        | ExecResult.returned v st' => some (ExecResult.returned v st')) =
      some (ExecResult.returned (.int (n + 1)) (st.withHeap (st.heap.write addr (.int (n + 1)))))
  have hMapWrite0 :
      Option.map ExecResult.normal
        (st.writePtr (addr : PtrVal) (.int (n + 1))) =
          some (ExecResult.normal st1) := by
    rw [hWritePtr]
    rfl
  rw [hMapWrite0]
  simp [hEvalRet, st1]

theorem increment_sgenVC (addr : Nat) (n : Int) :
    sgenVC (incrementSpec addr n) := by
  intro st hpre
  rcases hpre with ⟨hp, hheap⟩
  have hEvalP : evalExpr (.var "p") st = some (CVal.ptrAddr (addr : PtrVal)) := by
    simpa [evalExpr] using hp
  have hReadPtr : st.readPtr (addr : PtrVal) = some (.int n) := by
    simpa [hheap] using (CState.readPtr_block0 st addr addr)
  have hEvalDeref : evalExpr (.deref (.var "p")) st = some (.int n) := by
    simpa [evalExpr, evalStaticExpr, hEvalP] using hReadPtr
  have hStaticAdd :
      evalStaticExpr (.binop .add (.deref (.var "p")) (.intLit 1)) = none := by
    simp [evalStaticExpr]
  have hEvalOne : evalExpr (.intLit 1) st = some (.int 1) := by
    rfl
  have hEvalAdd :
      evalExpr (.binop .add (.deref (.var "p")) (.intLit 1)) st = some (.int (n + 1)) := by
    rw [evalExpr, hStaticAdd, hEvalDeref, hEvalOne]
    · rfl
    · intro h
      cases h
    · intro h
      cases h
  let st1 : CState := st.withHeap (st.heap.write addr (.int (n + 1)))
  have hWritePtr : st.writePtr (addr : PtrVal) (.int (n + 1)) = some st1 := by
    simpa [st1] using (CState.writePtr_block0 st addr addr (.int (n + 1)))
  have hp1 : st1.lookupVar "p" = some (CVal.ptrAddr (addr : PtrVal)) := by
    simpa [st1, CState.lookupVar] using hp
  have hEvalRet : evalExpr (.deref (.var "p")) st1 = some (.int (n + 1)) := by
    have hReadPtr1 : st1.readPtr (addr : PtrVal) = some (.int (n + 1)) := by
      calc
        st1.readPtr (addr : PtrVal) = st1.heap.read addr := by
          simpa using (CState.readPtr_block0 st1 addr addr)
        _ = some (.int (n + 1)) := by
          simpa [st1] using heap_read_write_eq st.heap addr (.int (n + 1))
    simpa [evalExpr, evalStaticExpr, hp1] using hReadPtr1
  have hretPost : swp (.ret (.deref (.var "p"))) (incrementSpec addr n).post st1 := by
    simp [swp, hEvalRet, incrementSpec, hp1, st1, heap_read_write_eq]
  have hpair :
      (∃ vOld, st.readPtr (addr : PtrVal) = some vOld) ∧
      ∃ st', st.writePtr (addr : PtrVal) (.int (n + 1)) = some st' ∧
        swp (.ret (.deref (.var "p"))) (incrementSpec addr n).post st' := by
    exact ⟨⟨.int n, hReadPtr⟩, ⟨st1, hWritePtr, hretPost⟩⟩
  simpa [incrementBody, swp, hEvalP, hEvalAdd, hEvalRet, incrementSpec, hp1, st1]
    using hpair

theorem callerFunEnv_sound (addr : Nat) (n : Int) :
    FunEnvSound (callerFunEnv addr n) := by
  intro fname spec hlookup
  by_cases hname : fname = "increment"
  · subst fname
    have hlookup' : some (incrementSpec addr n) = some spec := by
      simpa [callerFunEnv] using hlookup
    cases hlookup'
    refine ⟨?_, ?_, ?_, increment_sgenVC addr n⟩
    · simp [LoopFree, incrementSpec, incrementBody]
    · simp [TailReturn, NoReturn, incrementSpec, incrementBody]
    · simp [MustReturn, NoReturn, incrementSpec, incrementBody]
  · have : callerFunEnv addr n fname = none := by
      simp [callerFunEnv]
    rw [this] at hlookup
    cases hlookup

theorem execCall_increment (addr : Nat) (n : Int) :
    ∀ st,
      (callerSpec addr n).pre st →
      execCall (callerFunEnv addr n) 2 "increment" [.var "p"] st =
        some (.int (n + 1), st.withHeap (st.heap.write addr (.int (n + 1)))) := by
  intro st hpre
  rcases hpre with ⟨hp, hheap⟩
  have hEntryPre : (incrementSpec addr n).pre
      (callEntryState st (incrementSpec addr n) [CVal.ptrAddr (addr : PtrVal)]) := by
    refine ⟨?_, hheap⟩
    simpa using increment_entry_lookup_p st addr n
  have hExecInc :=
    increment_executes addr n
      (callEntryState st (incrementSpec addr n) [CVal.ptrAddr (addr : PtrVal)]) hEntryPre
  rw [increment_entry_state] at hExecInc
  have hCallBind :=
      congrArg
        (fun res =>
          Option.bind res (fun __do_lift =>
            match __do_lift with
            | .returned ret callee => some (ret, restoreCallerState st callee)
            | .normal callee => some (.undef, restoreCallerState st callee)))
        hExecInc
  simpa [execCall, callerFunEnv, evalArgs, hp, incrementSpec, callEntryState,
    bindCallEnv_single_p] using hCallBind

theorem caller_executes (addr : Nat) (n : Int) :
    ∀ st,
      (callerSpec addr n).pre st →
      ∃ st',
        execStmtFull (callerFunEnv addr n) 4 callerBody st =
          some (.returned (.int (n + 1)) st') ∧
        (callerSpec addr n).post (.int (n + 1)) st' := by
  intro st hpre
  rcases hpre with ⟨hp, hheap⟩
  have hcallSpec :
      swpCall (callerFunEnv addr n) "increment" [.var "p"]
        (fun ret st' =>
          ret = .int (n + 1) ∧
          st'.lookupVar "p" = some (CVal.ptrAddr (addr : PtrVal)) ∧
          st'.heap.read addr = some (.int (n + 1))) st := by
    apply swpCall_intro (funEnv := callerFunEnv addr n) (fname := "increment")
      (args := [.var "p"]) (spec := incrementSpec addr n) (vals := [CVal.ptrAddr (addr : PtrVal)])
      (Q := fun ret st' =>
        ret = .int (n + 1) ∧
        st'.lookupVar "p" = some (CVal.ptrAddr (addr : PtrVal)) ∧
        st'.heap.read addr = some (.int (n + 1)))
    · rfl
    · simp [evalArgs, hp]
    · simp [incrementSpec]
    · refine ⟨?_, hheap⟩
      simpa using increment_entry_lookup_p st addr n
    · intro ret callee hpost
      rcases hpost with ⟨hret, hpCallee, hheapCallee⟩
      refine ⟨hret, ?_, ?_⟩
      · simpa [restoreCallerState, CState.lookupVar] using hp
      · simpa [restoreCallerState] using hheapCallee
  have hcallFuel : callDepth (callerFunEnv addr n) "increment" ≤ 2 + 1 := by
    change stmtDepth (incrementSpec addr n).body + 1 ≤ 2 + 1
    simp [incrementSpec, incrementBody, stmtDepth]
  rcases execCall_sound (funEnv := callerFunEnv addr n) (callerFunEnv_sound addr n)
      hcallFuel hcallSpec with ⟨ret, stCall, hCall, hCallPost⟩
  have hEvalRet : evalExpr (.var "result") (stCall.updateVar "result" ret) = some ret := by
    simp [evalExpr, CState.lookupVar, CState.updateVar]
  refine ⟨stCall.updateVar "result" ret, ?_, ?_⟩
  · rcases hCallPost with ⟨hret, _, _⟩
    cases hret
    simp [execStmtFull, callerBody, hCall]
  · rcases hCallPost with ⟨hret, hpCall, hheapCall⟩
    refine ⟨rfl, ?_, hheapCall⟩
    calc
      (stCall.updateVar "result" ret).lookupVar "p" = stCall.lookupVar "p" := by
        simpa using lookupVar_updateVar_ne stCall "result" "p" ret
          (by decide : "p" ≠ "result")
      _ = some (CVal.ptrAddr (addr : PtrVal)) := hpCall

theorem xapp_smoke (addr : Nat) (n : Int) :
    ∀ st,
      (callerSpec addr n).pre st →
      swpCall (callerFunEnv addr n) "increment" [.var "p"] (fun _ _ => True) st := by
  intro st hpre
  rcases hpre with ⟨hp, hheap⟩
  apply swpCall_intro (funEnv := callerFunEnv addr n) (fname := "increment")
    (args := [.var "p"]) (spec := incrementSpec addr n)
    (vals := [CVal.ptrAddr (addr : PtrVal)]) (Q := fun _ _ => True)
  · rfl
  · simp [evalArgs, hp]
  · simp [incrementSpec]
  · refine ⟨?_, hheap⟩
    simpa using increment_entry_lookup_p st addr n
  · intro _ _ _
    trivial

end HeytingLean.LeanCP.Examples
