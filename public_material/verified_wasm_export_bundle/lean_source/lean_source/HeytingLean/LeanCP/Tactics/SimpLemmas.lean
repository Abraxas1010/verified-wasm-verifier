import HeytingLean.LeanCP.Tactics.Attrs
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Core.SFrameRule
import HeytingLean.LeanCP.Lang.StructLayout
import HeytingLean.LeanCP.VCG.RecCallSound

/-!
# LeanCP Forward-Tactic Lemma DB

This file centralizes the simp/unfold facts consumed by the Phase 5 forward
automation surface. The goal is to keep tactic macros generic and push
example-specific cleanup work into a tagged lemma database.
-/

namespace HeytingLean.LeanCP

attribute [simp, leancp_simp] lookup_updateVarEnv_ne
attribute [simp, leancp_simp] lookupVar_updateVar_eq
attribute [simp, leancp_simp] lookupVar_updateVar_ne
attribute [simp, leancp_simp] heap_read_write_eq
attribute [simp, leancp_simp] heap_read_write_ne
attribute [simp, leancp_simp] ofHProp_updateVar
attribute [simp, leancp_simp] updateVar_setHeap
attribute [simp, leancp_simp] CState.updateVar_withHeap
attribute [simp, leancp_simp] CState.withHeap_heap
attribute [simp, leancp_simp] CState.withHeap_env
attribute [simp, leancp_simp] CState.withHeap_nextAddr
attribute [simp, leancp_simp] CState.withHeap_mem
attribute [simp, leancp_simp] CState.withHeap_allocs
attribute [simp, leancp_simp] StructLayout.defaultFieldOffset_data
attribute [simp, leancp_simp] StructLayout.defaultFieldOffset_next
attribute [simp, leancp_simp] StructLayout.defaultFieldOffset_left
attribute [simp, leancp_simp] StructLayout.defaultFieldOffset_right
attribute [simp, leancp_simp] StructLayout.defaultFieldOffset_prev

@[simp, leancp_simp] theorem evalExpr_var_lookup (st : CState) (x : String) :
    evalExpr (.var x) st = st.lookupVar x := by
  rfl

@[simp, leancp_simp] theorem evalArgs_nil (st : CState) :
    evalArgs [] st = some [] := by
  simp [evalArgs]

@[simp, leancp_simp] theorem evalArgs_singleton (arg : CExpr) (st : CState) :
    evalArgs [arg] st = Option.map List.singleton (evalExpr arg st) := by
  cases h : evalExpr arg st <;> simp [evalArgs, h, List.singleton]

@[simp, leancp_simp] theorem bindCallEnv_nil :
    bindCallEnv [] [] = [] := by
  simp [bindCallEnv]

@[simp, leancp_simp] theorem callEntryState_heap (caller : CState) (spec : SFunSpec) (vals : List CVal) :
    (callEntryState caller spec vals).heap = caller.heap := by
  rfl

@[simp, leancp_simp] theorem callEntryState_nextAddr
    (caller : CState) (spec : SFunSpec) (vals : List CVal) :
    (callEntryState caller spec vals).nextAddr = caller.nextAddr := by
  rfl

@[simp, leancp_simp] theorem callEntryState_mem
    (caller : CState) (spec : SFunSpec) (vals : List CVal) :
    (callEntryState caller spec vals).mem = caller.mem := by
  rfl

@[simp, leancp_simp] theorem callEntryState_allocs
    (caller : CState) (spec : SFunSpec) (vals : List CVal) :
    (callEntryState caller spec vals).allocs = caller.allocs := by
  rfl

@[simp, leancp_simp] theorem restoreCallerState_lookup
    (caller callee : CState) (x : String) :
    (restoreCallerState caller callee).lookupVar x = caller.lookupVar x := by
  rfl

@[simp, leancp_simp] theorem restoreCallerState_heap
    (caller callee : CState) :
    (restoreCallerState caller callee).heap = callee.heap := by
  rfl

@[simp, leancp_simp] theorem restoreCallerState_mem
    (caller callee : CState) :
    (restoreCallerState caller callee).mem = callee.mem := by
  rfl

@[simp, leancp_simp] theorem restoreCallerState_allocs
    (caller callee : CState) :
    (restoreCallerState caller callee).allocs = callee.allocs := by
  rfl

@[simp, leancp_simp] theorem restoreCallerState_nextAddr
    (caller callee : CState) :
    (restoreCallerState caller callee).nextAddr = callee.nextAddr := by
  rfl

attribute [leancp_unfold] sgenVC
attribute [leancp_unfold] sgenVCFull
attribute [leancp_unfold] swp
attribute [leancp_unfold] swpFull
attribute [leancp_unfold] swpCall
attribute [leancp_unfold] swhileWP
attribute [leancp_unfold] swhileWPFull
attribute [leancp_unfold] evalArgs
attribute [leancp_unfold] callEntryState
attribute [leancp_unfold] restoreCallerState
attribute [leancp_unfold] bindCallEnv

end HeytingLean.LeanCP
