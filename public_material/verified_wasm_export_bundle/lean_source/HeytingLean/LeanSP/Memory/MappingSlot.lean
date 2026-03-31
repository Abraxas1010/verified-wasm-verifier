import HeytingLean.LeanSP.Lang.EVMPrimops

/-!
# LeanSP.Memory.MappingSlot

Formalization of Solidity's keccak256-based mapping storage slot addressing.

Reference: https://docs.soliditylang.org/en/latest/internals/layout_in_storage.html
"The value corresponding to a mapping key k is located at keccak256(h(k) . p)
 where . is concatenation and p is the storage slot of the mapping declaration."

For `mapping(address => uint256)` or `mapping(uint256 => uint256)`, the key is
a value type, so `h(k)` pads the value to 32 bytes in big-endian format —
which is exactly `word256ToBytesBE`.

## What is verified
- `mappingSlot` definition matching the Solidity specification
- Non-interference: distinct keys → distinct slots (via `keccak256_collision_resistant`)
- Cross-mapping non-interference: same key in different mappings → distinct slots
- Storage read/write lemmas lifted to mapping slots

## Honest boundary
The proofs require `abiEncodePair` to produce distinct byte arrays for distinct
inputs. We take this as an explicit hypothesis (`hEncNe`) rather than proving
byte-level injectivity of `word256ToBytesBE`, because the byte-level proof
requires reasoning about the encoding loop that is not yet automated.
For concrete slot addresses (e.g., in tests), the hypothesis is dischargeable
by `native_decide`.
-/

namespace LeanSP.Memory

open LeanSP.Arith
open LeanSP.EVM

/-- ABI-encode two Word256 values as 64 bytes (32 + 32, big-endian).
    Matches Solidity's `abi.encode(uint256, uint256)` for storage slot computation. -/
def abiEncodePair (a b : Word256) : ByteArray :=
  word256ToBytesBE a ++ word256ToBytesBE b

/-- Solidity mapping slot: `keccak256(h(key) . baseSlot)`.
    `baseSlot` is the declaration slot of the mapping in the contract's storage layout. -/
def mappingSlot (key baseSlot : Word256) : Word256 :=
  keccak256Hash (abiEncodePair key baseSlot)

-- ==========================================
-- Non-interference theorems
-- ==========================================

/-- Mapping slot non-interference: distinct keys in the same mapping
    map to distinct slots (via keccak256 collision resistance).
    The `hEncNe` hypothesis is the encoding injectivity precondition. -/
theorem mappingSlot_ne (k1 k2 baseSlot : Word256)
    (hEncNe : abiEncodePair k1 baseSlot ≠ abiEncodePair k2 baseSlot) :
    mappingSlot k1 baseSlot ≠ mappingSlot k2 baseSlot := by
  unfold mappingSlot
  exact keccak256_collision_resistant _ _ hEncNe

/-- Cross-mapping non-interference: same key in different mappings
    (different base slots) maps to distinct slots. -/
theorem mappingSlot_cross_ne (key s1 s2 : Word256)
    (hEncNe : abiEncodePair key s1 ≠ abiEncodePair key s2) :
    mappingSlot key s1 ≠ mappingSlot key s2 := by
  unfold mappingSlot
  exact keccak256_collision_resistant _ _ hEncNe

-- ==========================================
-- Storage lemmas lifted to mapping slots
-- ==========================================

/-- Storage non-interference for mapping-addressed slots. -/
theorem sload_sstore_mapping_ne (storage : EVMStorage) (k1 k2 baseSlot v : Word256)
    (hSlotNe : (mappingSlot k1 baseSlot == mappingSlot k2 baseSlot) = false) :
    (storage.sstore (mappingSlot k2 baseSlot) v).sload (mappingSlot k1 baseSlot) =
    storage.sload (mappingSlot k1 baseSlot) :=
  EVMStorage.sload_sstore_ne storage (mappingSlot k1 baseSlot) (mappingSlot k2 baseSlot) v hSlotNe

/-- Read-after-write for mapping slots. -/
theorem sload_sstore_mapping_same (storage : EVMStorage) (key baseSlot v : Word256) :
    (storage.sstore (mappingSlot key baseSlot) v).sload (mappingSlot key baseSlot) = v :=
  EVMStorage.sload_sstore_same storage (mappingSlot key baseSlot) v

/-- Mapping slot doesn't interfere with fixed slots. -/
theorem sload_sstore_mapping_fixed_ne (storage : EVMStorage) (key baseSlot : Word256)
    (fixedSlot v : Word256)
    (hNe : (fixedSlot == mappingSlot key baseSlot) = false) :
    (storage.sstore (mappingSlot key baseSlot) v).sload fixedSlot =
    storage.sload fixedSlot :=
  EVMStorage.sload_sstore_ne storage fixedSlot (mappingSlot key baseSlot) v hNe

end LeanSP.Memory
