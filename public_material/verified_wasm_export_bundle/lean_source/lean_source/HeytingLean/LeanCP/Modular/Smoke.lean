import HeytingLean.LeanCP.Modular.Linking
import HeytingLean.LeanCP.Examples.CallerVerified

/-!
# LeanCP Modular Verification Smoke

This smoke surface links a provider unit exporting `increment` with a client
unit exporting `caller` and importing `increment`.
-/

namespace HeytingLean.LeanCP.Modular.Smoke

open HeytingLean.LeanCP
open HeytingLean.LeanCP.Examples
open HeytingLean.LeanCP.Modular

def incrementOnlyEnv (addr : Nat) (n : Int) : FunEnv
  | "increment" => some (incrementSpec addr n)
  | _ => none

def callerModuleEnv (addr : Nat) (n : Int) : FunEnv
  | "increment" => some (incrementSpec addr n)
  | "caller" => some (callerSpec addr n)
  | _ => none

theorem increment_sgenVCFull (addr : Nat) (n : Int) :
    sgenVCFull (incrementOnlyEnv addr n) (incrementSpec addr n) := by
  intro st hpre
  simpa [sgenVCFull, swpFull, swp, incrementOnlyEnv] using increment_sgenVC addr n st hpre

theorem caller_sgenVCFull (addr : Nat) (n : Int) :
    sgenVCFull (callerModuleEnv addr n) (callerSpec addr n) := by
  intro st hpre
  rcases hpre with ⟨hp, hheap⟩
  apply swpCall_intro (funEnv := callerModuleEnv addr n) (fname := "increment")
    (args := [.var "p"]) (spec := incrementSpec addr n)
    (vals := [CVal.ptrAddr (addr : PtrVal)])
    (Q := fun ret st' =>
      swpFull (callerModuleEnv addr n) (.ret (.var "result"))
        (callerSpec addr n).post (st'.updateVar "result" ret))
  · simp [callerModuleEnv]
  · simp [evalArgs, hp]
  · simp [incrementSpec]
  · refine ⟨?_, hheap⟩
    simp [callEntryState, incrementSpec, bindCallEnv, CState.lookupVar]
  · intro ret callee hinc
    rcases hinc with ⟨hret, hpCallee, hheapCallee⟩
    have hEval :
        evalExpr (.var "result") ((restoreCallerState st callee).updateVar "result" ret) = some ret := by
      simp [evalExpr, CState.lookupVar, CState.updateVar]
    have hpAfter :
        ((restoreCallerState st callee).updateVar "result" ret).lookupVar "p" =
          some (CVal.ptrAddr (addr : PtrVal)) := by
      calc
        ((restoreCallerState st callee).updateVar "result" ret).lookupVar "p" =
            (restoreCallerState st callee).lookupVar "p" := by
          simpa using lookupVar_updateVar_ne (restoreCallerState st callee) "result" "p" ret
            (by decide : "p" ≠ "result")
        _ = st.lookupVar "p" := by
          simp [restoreCallerState, CState.lookupVar]
        _ = some (CVal.ptrAddr (addr : PtrVal)) := hp
    have hheapAfter :
        ((restoreCallerState st callee).updateVar "result" ret).heap.read addr =
          some (.int (n + 1)) := by
      simpa [restoreCallerState, CState.updateVar] using hheapCallee
    simpa [swpFull, hEval, callerSpec] using
      (show ret = .int (n + 1) ∧
          ((restoreCallerState st callee).updateVar "result" ret).lookupVar "p" =
            some (CVal.ptrAddr (addr : PtrVal)) ∧
          ((restoreCallerState st callee).updateVar "result" ret).heap.read addr =
            some (.int (n + 1)) from
        ⟨hret, hpAfter, hheapAfter⟩)

def incrementProc (addr : Nat) (n : Int) : VerifiedProc where
  spec := incrementSpec addr n
  verifyEnv := incrementOnlyEnv addr n
  sound := by
    refine ⟨?_, ?_, ?_, increment_sgenVCFull addr n⟩
    · simp [incrementSpec, incrementBody, LoopFree]
    · simp [incrementSpec, incrementBody, TailReturn, NoReturn]
    · simp [incrementSpec, incrementBody, MustReturn, NoReturn]

def callerProc (addr : Nat) (n : Int) : VerifiedProc where
  spec := callerSpec addr n
  verifyEnv := callerModuleEnv addr n
  sound := by
    refine ⟨?_, ?_, ?_, caller_sgenVCFull addr n⟩
    · simp [callerSpec, callerBody, LoopFree]
    · simp [callerSpec, callerBody, TailReturn, NoReturn]
    · simp [callerSpec, callerBody, MustReturn, NoReturn]

def incrementUnit (addr : Nat) (n : Int) : VSU where
  name := "increment_unit"
  imports := []
  exports := [incrementProc addr n]
  exports_nodup := by simp [procNames, incrementProc]

def callerUnit (addr : Nat) (n : Int) : VSU where
  name := "caller_unit"
  imports := ["increment"]
  exports := [callerProc addr n]
  exports_nodup := by simp [procNames, callerProc]

theorem modular_link_ok (addr : Nat) (n : Int) :
    ∃ u, link (incrementUnit addr n) (callerUnit addr n) = some u := by
  refine ⟨compose (incrementUnit addr n) (callerUnit addr n) ?_, ?_⟩
  · intro name hleft hright
    simp [incrementUnit, callerUnit, VSU.exportNames, procNames,
      incrementProc, callerProc, incrementSpec, callerSpec] at hleft hright
    subst name
    simp at hright
  · exact link_eq_some

theorem linked_caller_sound (addr : Nat) (n : Int) :
    ∃ u, link (incrementUnit addr n) (callerUnit addr n) = some u ∧
      VSU.exportSound u "caller" := by
  rcases modular_link_ok addr n with ⟨u, hlink⟩
  refine ⟨u, hlink, ?_⟩
  simpa [callerSpec] using
    (link_right_export_sound (u1 := incrementUnit addr n) (u2 := callerUnit addr n)
      (u := u) hlink (proc := callerProc addr n) (by simp [callerUnit]))

theorem linked_increment_resolves_client_import (addr : Nat) (n : Int) :
    ∃ u, link (incrementUnit addr n) (callerUnit addr n) = some u ∧
      "increment" ∉ u.imports := by
  rcases modular_link_ok addr n with ⟨u, hlink⟩
  refine ⟨u, hlink, ?_⟩
  exact link_resolves_right_import hlink
    (by simp [callerUnit])
    (by simp [incrementUnit, VSU.exportNames, procNames, incrementProc, incrementSpec])
    (by simp [incrementUnit])

end HeytingLean.LeanCP.Modular.Smoke
