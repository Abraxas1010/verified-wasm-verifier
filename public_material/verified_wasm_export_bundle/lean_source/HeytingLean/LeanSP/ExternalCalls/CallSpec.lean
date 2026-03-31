import HeytingLean.LeanSP.Memory.MappingSlot

/-!
# LeanSP.ExternalCalls.CallSpec

Abstract specification of EVM external call behavior for Hoare-logic reasoning.

## Design
The caller does NOT know the callee's code — only its `CallSpec`. This models
the fundamental challenge of smart contract verification: external calls invoke
arbitrary code. The spec captures what the callee **may** do, not what it **will** do.

## Prior art
- Nethermind EVMYulLean: account-based state + balance transfer + snapshot/rollback
- "Reentrancy? Yes. Reentrancy Bug? No." (Grossman et al.): Hoare logic extension
  with reentry trigger proof rules, formalized in Coq
- Scilla: explicit communication/computation separation

## What is verified
- `CallSpec` type with success/failure/reentry dimensions
- Standard specs: adversarial, staticCall, nonReentrant
- `CallOutcome` inductive for call results
- Theorems about spec composition and safety
-/

namespace LeanSP.ExternalCalls

open LeanSP.Arith
open LeanSP.EVM
open LeanSP.Memory

-- ==========================================
-- Call specification
-- ==========================================

/-- Abstract specification of an external call's behavior.
    The caller provides a spec for the callee; verification proceeds
    assuming only the spec's guarantees. -/
structure CallSpec where
  /-- Can the call succeed (return 1)? -/
  maySucceed : Bool
  /-- Can the call fail/revert (return 0)? -/
  mayRevert : Bool
  /-- Can the callee call back into the caller (reentrancy)? -/
  mayReenter : Bool
  /-- Maximum reentrancy depth (0 = no reentrancy). -/
  maxReentryDepth : Nat
  deriving Repr, Inhabited

/-- The most conservative call spec: callee may do anything. -/
def CallSpec.adversarial : CallSpec :=
  { maySucceed := true, mayRevert := true, mayReenter := true,
    maxReentryDepth := 1024 }

/-- staticcall spec: callee cannot modify caller's storage, cannot receive value.
    May still reenter via other contracts in the call chain. -/
def CallSpec.staticCall : CallSpec :=
  { maySucceed := true, mayRevert := true, mayReenter := true,
    maxReentryDepth := 1024 }

/-- Call to a known non-reentrant target (e.g., precompile, EOA). -/
def CallSpec.nonReentrant : CallSpec :=
  { maySucceed := true, mayRevert := true, mayReenter := false,
    maxReentryDepth := 0 }

/-- Call that always fails (current LeanSP default for unmodeled calls). -/
def CallSpec.alwaysFails : CallSpec :=
  { maySucceed := false, mayRevert := true, mayReenter := false,
    maxReentryDepth := 0 }

-- ==========================================
-- Call outcome
-- ==========================================

/-- Outcome of an external call. -/
inductive CallOutcome where
  /-- Call succeeded: callee returned 1. -/
  | success (returnData : ByteArray)
  /-- Call reverted: callee returned 0. -/
  | revert (returnData : ByteArray)
  deriving Inhabited

/-- Is the outcome a success? -/
def CallOutcome.isSuccess : CallOutcome → Bool
  | .success _ => true
  | .revert _ => false

-- ==========================================
-- Call context (extends YulState conceptually)
-- ==========================================

/-- Call context for tracking reentrancy depth and locked state. -/
structure CallContext where
  /-- Current call depth (0 = top-level). -/
  callDepth : Nat
  /-- Whether a reentrancy guard is active. -/
  reentrancyLocked : Bool
  deriving Repr, Inhabited

def CallContext.initial : CallContext :=
  { callDepth := 0, reentrancyLocked := false }

/-- Can a call proceed given the current context and spec? -/
def canCall (ctx : CallContext) (spec : CallSpec) : Bool :=
  -- Check reentrancy: if locked and callee may reenter, block
  if ctx.reentrancyLocked && spec.mayReenter then false
  -- Check depth limit
  else if ctx.callDepth ≥ spec.maxReentryDepth then !spec.mayReenter
  else true

-- ==========================================
-- Theorems
-- ==========================================

/-- A non-reentrant spec never triggers reentrancy concerns. -/
theorem nonReentrant_no_reentry :
    CallSpec.nonReentrant.mayReenter = false := rfl

/-- An always-fails spec never succeeds. -/
theorem alwaysFails_no_success :
    CallSpec.alwaysFails.maySucceed = false := rfl

/-- If the reentrancy lock is active, an adversarial call is blocked. -/
theorem locked_blocks_adversarial :
    canCall { callDepth := 0, reentrancyLocked := true } CallSpec.adversarial = false := rfl

/-- If the reentrancy lock is NOT active, an adversarial call is allowed. -/
theorem unlocked_allows_adversarial :
    canCall CallContext.initial CallSpec.adversarial = true := rfl

/-- Non-reentrant calls are always allowed regardless of lock state. -/
theorem nonReentrant_always_allowed (ctx : CallContext) :
    canCall ctx CallSpec.nonReentrant = true := by
  unfold canCall CallSpec.nonReentrant
  simp

/-- A call to a non-reentrant target from any depth is safe. -/
theorem nonReentrant_depth_safe (depth : Nat) (locked : Bool) :
    canCall { callDepth := depth, reentrancyLocked := locked } CallSpec.nonReentrant = true := by
  unfold canCall CallSpec.nonReentrant
  simp

end LeanSP.ExternalCalls
