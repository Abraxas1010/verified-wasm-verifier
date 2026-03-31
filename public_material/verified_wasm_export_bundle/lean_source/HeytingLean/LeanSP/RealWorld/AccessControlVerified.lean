import HeytingLean.LeanSP.Verify.VCDischarge

/-!
# LeanSP.RealWorld.AccessControlVerified

Verified Ownable access control pattern.
-/

namespace LeanSP.RealWorld

open LeanSP.Arith
open LeanSP.EVM
open LeanSP.Memory

def ownerSlot : Word256 := Word256.zero

/-- Frame property: functions not writing to ownerSlot don't change the owner. -/
theorem owner_frame (storage : EVMStorage) (k v : Word256)
    (hNe : (ownerSlot == k) = false) :
    (storage.sstore k v).sload ownerSlot = storage.sload ownerSlot :=
  EVMStorage.sload_sstore_ne storage ownerSlot k v hNe

/-- Owner can be read after being set. -/
theorem owner_set_read (storage : EVMStorage) (newOwner : Word256) :
    (storage.sstore ownerSlot newOwner).sload ownerSlot = newOwner :=
  EVMStorage.sload_sstore_same storage ownerSlot newOwner

/-- Initial owner is zero (empty storage). -/
theorem owner_initial :
    EVMStorage.empty.sload ownerSlot = Word256.zero :=
  EVMStorage.sload_empty ownerSlot

end LeanSP.RealWorld
