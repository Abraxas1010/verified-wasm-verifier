import HeytingLean.LeanSP.Arith.Word256

/-!
# LeanSP.Memory.EVMMemory

Byte-addressed expandable EVM memory model.
MLOAD reads 32-byte big-endian chunks; MSTORE writes 32-byte big-endian chunks.
Memory starts empty and expands (zero-filled) on access.
-/

namespace LeanSP.Memory

open LeanSP.Arith

/-- EVM memory: byte-addressable, zero-initialized, expandable. -/
structure EVMMemory where
  data : ByteArray
  deriving Inhabited

/-- Empty memory (initial state). -/
def EVMMemory.empty : EVMMemory := ⟨ByteArray.empty⟩

/-- Expand memory to at least `size` bytes (zero-filled). -/
def EVMMemory.expand (mem : EVMMemory) (size : Nat) : EVMMemory :=
  if mem.data.size ≥ size then mem
  else ⟨mem.data ++ ByteArray.mk (Array.mkArray (size - mem.data.size) 0)⟩

/-- Current memory size in bytes. -/
def EVMMemory.size (mem : EVMMemory) : Nat := mem.data.size

/-- EVM MSIZE: memory size rounded up to nearest 32-byte word. -/
def EVMMemory.msize (mem : EVMMemory) : Word256 :=
  BitVec.ofNat 256 (((mem.data.size + 31) / 32) * 32)

/-- EVM MLOAD: read 32 bytes from offset as big-endian Word256. -/
def EVMMemory.mload (mem : EVMMemory) (offset : Nat) : Word256 × EVMMemory :=
  let mem := mem.expand (offset + 32)
  (bytesToWord256BE mem.data offset, mem)

/-- EVM MSTORE: write Word256 as 32 big-endian bytes at offset. -/
def EVMMemory.mstore (mem : EVMMemory) (offset : Nat) (val : Word256) : EVMMemory := Id.run do
  let mem := mem.expand (offset + 32)
  let bytes := word256ToBytesBE val
  let mut data := mem.data
  for i in [:32] do
    data := data.set! (offset + i) (bytes.get! i)
  return ⟨data⟩

/-- EVM MSTORE8: write a single byte at offset. -/
def EVMMemory.mstore8 (mem : EVMMemory) (offset : Nat) (val : Word256) : EVMMemory :=
  let mem := mem.expand (offset + 1)
  let byte := UInt8.ofNat (val.toNat % 256)
  ⟨mem.data.set! offset byte⟩

/-- EVM CALLDATALOAD: read 32 bytes from calldata at offset (zero-padded). -/
def calldataLoad (calldata : ByteArray) (offset : Nat) : Word256 :=
  bytesToWord256BE (calldata ++ ByteArray.mk (Array.mkArray 32 0)) offset

/-- EVM CALLDATACOPY: copy calldata region to memory. -/
def EVMMemory.calldatacopy (mem : EVMMemory) (destOffset cdOffset size : Nat)
    (calldata : ByteArray) : EVMMemory := Id.run do
  if size == 0 then return mem
  let mem := mem.expand (destOffset + size)
  let mut data := mem.data
  for i in [:size] do
    let byte := if cdOffset + i < calldata.size then calldata.get! (cdOffset + i) else 0
    data := data.set! (destOffset + i) byte
  return ⟨data⟩

end LeanSP.Memory
