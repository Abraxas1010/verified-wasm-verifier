import HeytingLean.LeanSP.ExternalCalls.CallSpec
import HeytingLean.LeanSP.Verify.VCDischarge

/-!
# LeanSP.ExternalCalls.ReentrancyGuard

Formal verification of the ReentrancyGuard pattern.

The guard uses a storage slot as a mutex:
1. Read the lock slot; if nonzero, revert (already locked)
2. Write 1 to the lock slot (lock)
3. Execute external call
4. Write 0 to the lock slot (unlock)

If a reentrant call hits step 1 while the lock is held, it reverts.

## What is verified
- Guard lock/unlock preserves storage frame (non-guard slots unaffected)
- Lock is visible: after locking, sload returns 1
- Unlock restores: after unlocking, sload returns 0
- Reentry blocked: if locked, reentering function sees lock = 1
- Concrete pipeline tests: Yul AST for the guard pattern
-/

namespace LeanSP.ExternalCalls

open LeanSP.Arith
open LeanSP.EVM
open LeanSP.Memory
open LeanSP.Verify
open LeanSP.Yul

-- ==========================================
-- Reentrancy guard slot
-- ==========================================

/-- Conventional reentrancy guard storage slot.
    OpenZeppelin uses keccak256("ReentrancyGuard") - 1; we use slot 0
    for simplicity in the formalization. -/
def guardSlot : Word256 := Word256.zero

-- ==========================================
-- Storage properties of the guard
-- ==========================================

/-- After locking (sstore guardSlot 1), the guard slot reads as 1. -/
theorem guard_lock_visible (storage : EVMStorage) :
    (storage.sstore guardSlot Word256.one).sload guardSlot = Word256.one :=
  EVMStorage.sload_sstore_same storage guardSlot Word256.one

/-- After unlocking (sstore guardSlot 0), the guard slot reads as 0. -/
theorem guard_unlock_restores (storage : EVMStorage) :
    (storage.sstore guardSlot Word256.zero).sload guardSlot = Word256.zero :=
  EVMStorage.sload_sstore_same storage guardSlot Word256.zero

/-- Locking does not affect other storage slots. -/
theorem guard_lock_frame (storage : EVMStorage) (otherSlot : Word256)
    (hNe : (otherSlot == guardSlot) = false) :
    (storage.sstore guardSlot Word256.one).sload otherSlot =
    storage.sload otherSlot :=
  EVMStorage.sload_sstore_ne storage otherSlot guardSlot Word256.one hNe

/-- Unlocking does not affect other storage slots. -/
theorem guard_unlock_frame (storage : EVMStorage) (otherSlot : Word256)
    (hNe : (otherSlot == guardSlot) = false) :
    (storage.sstore guardSlot Word256.zero).sload otherSlot =
    storage.sload otherSlot :=
  EVMStorage.sload_sstore_ne storage otherSlot guardSlot Word256.zero hNe

/-- If the guard is locked (slot = 1), a reentrant call sees the lock.
    This is the key safety property: the reentrant call's guard check
    reads 1, which triggers revert. -/
theorem guard_reentry_sees_lock (storage : EVMStorage)
    (hLocked : storage.sload guardSlot = Word256.one) :
    storage.sload guardSlot ≠ Word256.zero := by
  rw [hLocked]; unfold Word256.one Word256.zero; intro h; simp at h

/-- Full lock-unlock cycle: after lock then unlock, guard slot is back to 0. -/
theorem guard_lock_unlock_cycle (storage : EVMStorage) :
    ((storage.sstore guardSlot Word256.one).sstore guardSlot Word256.zero).sload guardSlot =
    Word256.zero := by
  simp [EVMStorage.sload_sstore_same]

/-- The lock-unlock cycle preserves non-guard storage slots. -/
theorem guard_cycle_frame (storage : EVMStorage) (otherSlot : Word256)
    (hNe : (otherSlot == guardSlot) = false) :
    ((storage.sstore guardSlot Word256.one).sstore guardSlot Word256.zero).sload otherSlot =
    storage.sload otherSlot := by
  rw [EVMStorage.sload_sstore_ne _ _ _ _ hNe]
  rw [EVMStorage.sload_sstore_ne _ _ _ _ hNe]

-- ==========================================
-- Yul AST: Reentrancy guard pattern
-- ==========================================

/-- Reentrancy guard: check lock, lock, (placeholder for call), unlock.
    The call body is left as a parameter — in practice it contains
    the external call statement. -/
def reentrancyGuardBody : List Stmt :=
  [ .assign "locked" (.call "sload" #[.nat 0]),
    .if_ (.ident "locked") #[.revert #[.nat 0, .nat 0]],
    .expr (.call "sstore" #[.nat 0, .nat 1]),
    -- External call would go here
    .expr (.call "sstore" #[.nat 0, .nat 0]),
    .assign "done" (.nat 1) ]

-- Concrete test: guard succeeds on first entry (slot 0 = 0)
#guard (match execSimpleBlock reentrancyGuardBody
    (mkYulState [("locked", BitVec.ofNat 256 0),
                 ("done", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "done" == some (BitVec.ofNat 256 1)
  | _ => false) == true

-- Concrete test: guard reverts on reentry (slot 0 = 1)
-- Simulating: the reentrant call enters with guard slot already = 1
-- We set "locked" initial value to 0 but storage has slot 0 = 1
-- The sload reads 1, then the if check reverts.
-- For the simple evaluator, we model this by pre-setting locked = 0
-- and having the sload read from the EVM state. But the simple evaluator
-- uses variable state, not EVM storage, so we test the guard logic directly
-- by pre-computing what sload would return.

-- Test: if sload returns 1 (simulated as locked=1 after first sload), guard reverts
def reentrancyGuardReentryBody : List Stmt :=
  [ .if_ (.ident "locked") #[.revert #[.nat 0, .nat 0]],
    .assign "done" (.nat 1) ]

#guard (match execSimpleBlock reentrancyGuardReentryBody
    (mkYulState [("locked", BitVec.ofNat 256 1),
                 ("done", BitVec.ofNat 256 0)]) with
  | .revert _ => true
  | _ => false) == true

-- Test: if locked = 0, guard passes
#guard (match execSimpleBlock reentrancyGuardReentryBody
    (mkYulState [("locked", BitVec.ofNat 256 0),
                 ("done", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "done" == some (BitVec.ofNat 256 1)
  | _ => false) == true

-- ==========================================
-- VC discharge tests
-- ==========================================

#guard (dischargeVC "guard_first_entry"
    reentrancyGuardBody
    (mkYulState [("locked", BitVec.ofNat 256 0),
                 ("done", BitVec.ofNat 256 0)])
    (fun st => VarStore.get? st.vars "done" == some (BitVec.ofNat 256 1))
  matches .discharged _) == true

#guard (dischargeVC "guard_reentry_blocked"
    reentrancyGuardReentryBody
    (mkYulState [("locked", BitVec.ofNat 256 1),
                 ("done", BitVec.ofNat 256 0)])
    (fun _ => true)
  matches .reverted _) == true

end LeanSP.ExternalCalls
