import HeytingLean.LeanSP.RealWorld.ERC20Verified

/-!
# LeanSP.Tests.ERC20Tests

Phase 5 gate tests for ERC-20 verification.
-/

namespace LeanSP.Tests

open LeanSP.Arith
open LeanSP.Memory
open LeanSP.RealWorld

-- Test 1: Storage read-after-write (foundation for ERC-20 proofs)
#eval do
  let store := EVMStorage.empty
  let store := store.sstore (BitVec.ofNat 256 1) (BitVec.ofNat 256 100)
  let v := store.sload (BitVec.ofNat 256 1)
  return s!"Test 1: sload after sstore = {v.toNat}"  -- expect 100

-- Test 2: Storage non-interference
#eval do
  let store := EVMStorage.empty
  let store := store.sstore (BitVec.ofNat 256 1) (BitVec.ofNat 256 100)
  let store := store.sstore (BitVec.ofNat 256 2) (BitVec.ofNat 256 200)
  let v1 := store.sload (BitVec.ofNat 256 1)
  let v2 := store.sload (BitVec.ofNat 256 2)
  return s!"Test 2: slot1={v1.toNat}, slot2={v2.toNat}"  -- expect 100, 200

-- Test 3: Empty storage reads as 0
#eval do
  let store := EVMStorage.empty
  let v := store.sload (BitVec.ofNat 256 42)
  return s!"Test 3: empty slot = {v.toNat}"  -- expect 0

end LeanSP.Tests
