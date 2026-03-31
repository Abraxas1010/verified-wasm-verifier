import HeytingLean.LeanCP.Examples.CallerVerified
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

attribute [leancp_unfold] callerBody
attribute [leancp_unfold] incrementBody

theorem caller_executes_tactic (addr : Nat) (n : Int) :
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
      (args := [.var "p"]) (spec := incrementSpec addr n)
      (vals := [CVal.ptrAddr (addr : PtrVal)])
    · simp [callerFunEnv]
    · simp [evalArgs, hp]
    · simp [incrementSpec]
    · refine ⟨?_, hheap⟩
      simp [incrementSpec, callEntryState, bindCallEnv, CState.lookupVar]
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
    simp [CState.lookupVar, CState.updateVar]
  have hpResult : "p" ≠ "result" := by decide
  refine ⟨stCall.updateVar "result" ret, ?_, ?_⟩
  · rcases hCallPost with ⟨hret, _, _⟩
    cases hret
    simp [execStmtFull, callerBody, hCall]
  · rcases hCallPost with ⟨hret, hpCall, hheapCall⟩
    refine ⟨rfl, ?_, hheapCall⟩
    calc
      (stCall.updateVar "result" ret).lookupVar "p" = stCall.lookupVar "p" := by
        simpa using lookupVar_updateVar_ne stCall "result" "p" ret
          hpResult
      _ = some (CVal.ptrAddr (addr : PtrVal)) := hpCall

theorem xapp_smoke_tactic (addr : Nat) (n : Int) :
    ∀ st,
      (callerSpec addr n).pre st →
      swpCall (callerFunEnv addr n) "increment" [.var "p"] (fun _ _ => True) st := by
  intro st hpre
  rcases hpre with ⟨hp, hheap⟩
  apply swpCall_intro (funEnv := callerFunEnv addr n) (fname := "increment")
    (args := [.var "p"]) (spec := incrementSpec addr n)
    (vals := [CVal.ptrAddr (addr : PtrVal)]) (Q := fun _ _ => True)
  · simp [callerFunEnv]
  · simp [evalArgs, hp]
  · simp [incrementSpec]
  · refine ⟨?_, hheap⟩
    simp [incrementSpec, callEntryState, bindCallEnv, CState.lookupVar]
  · intro _ _ _
    trivial

end HeytingLean.LeanCP.Examples
