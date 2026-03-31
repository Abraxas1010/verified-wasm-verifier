import HeytingLean.LeanSP.Arith.Word256

/-!
# LeanSP.Memory.EVMStorage

Word-addressed persistent EVM storage model.
Uses a function model `Word256 → Word256` for proof-friendly reasoning
(read-after-write, non-interference are trivially provable).
An efficient HashMap-backed version is available for computational use.
-/

namespace LeanSP.Memory

open LeanSP.Arith

/-- EVM storage as a function from slot to value.
    Default value is 0 for all uninitialized slots. -/
structure EVMStorage where
  /-- Storage function: maps each slot key to its current value. -/
  fn : Word256 → Word256
  deriving Inhabited

/-- Empty storage (all slots return 0). -/
def EVMStorage.empty : EVMStorage := ⟨fun _ => Word256.zero⟩

/-- EVM SLOAD: read storage slot. -/
@[inline] def EVMStorage.sload (store : EVMStorage) (key : Word256) : Word256 :=
  store.fn key

/-- EVM SSTORE: write storage slot. -/
@[inline] def EVMStorage.sstore (store : EVMStorage) (key val : Word256) : EVMStorage :=
  ⟨fun k => if k == key then val else store.fn k⟩

-- ==========================================
-- Storage reasoning lemmas (all proved)
-- ==========================================

/-- Read-after-write: reading a slot just written returns the written value. -/
@[simp] theorem EVMStorage.sload_sstore_same (store : EVMStorage) (k v : Word256) :
    (store.sstore k v).sload k = v := by
  simp [sload, sstore]

/-- Non-interference: writing to one slot doesn't affect reads of different slots. -/
@[simp] theorem EVMStorage.sload_sstore_ne (store : EVMStorage) (k1 k2 v : Word256)
    (hne : (k1 == k2) = false) :
    (store.sstore k2 v).sload k1 = store.sload k1 := by
  unfold sload sstore
  simp [hne]

/-- Empty storage reads as 0. -/
@[simp] theorem EVMStorage.sload_empty (k : Word256) :
    EVMStorage.empty.sload k = Word256.zero := by
  simp [sload, empty]

/-- Writing 0 to an empty slot is identity. -/
theorem EVMStorage.sstore_zero_empty (k : Word256) :
    ∀ x, (EVMStorage.empty.sstore k Word256.zero).sload x = EVMStorage.empty.sload x := by
  intro x; simp [sload, sstore, empty]

end LeanSP.Memory

-- NOTE: Mapping slot definitions (mappingSlot, abiEncodePair) and their proofs
-- are in LeanSP.Memory.MappingSlot to avoid circular imports with EVMPrimops.
