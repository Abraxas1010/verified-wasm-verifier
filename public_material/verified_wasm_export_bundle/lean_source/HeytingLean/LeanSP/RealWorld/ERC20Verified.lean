import HeytingLean.LeanSP.Verify.VCDischarge

/-!
# LeanSP.RealWorld.ERC20Verified

Helper lemmas for ERC-20 balance arithmetic and storage operations:
- `balance_conservation`: two-party balance sum preservation under add/sub
- `balance_slot_frame`: storage non-interference across distinct balance slots
- `balance_slot_update`: storage read-after-write for the written slot
- `balance_transfer_noninterference`: third-party balance unaffected by transfer

These are building blocks for a transfer correctness proof. The full transfer
Hoare triple (connecting Yul AST → execution → balance update) is not yet
formalized in this module.
-/

namespace LeanSP.RealWorld

open LeanSP.Arith
open LeanSP.EVM
open LeanSP.Memory

def totalSupplySlot : Word256 := Word256.zero
def balanceSlot (addr : Word256) : Word256 := keccak256Hash (word256ToBytesBE addr)

/-- Transfer precondition: sender has sufficient balance. -/
def transferPre (sender amount : Word256) (storage : EVMStorage) : Prop :=
  (storage.sload (balanceSlot sender)).toNat ≥ amount.toNat

/-- ERC-20 balance conservation: total of two balances is preserved. -/
theorem balance_conservation (senderBal receiverBal amount : Word256)
    (hSuf : senderBal.toNat ≥ amount.toNat)
    (hNoOverflow : receiverBal.toNat + amount.toNat < 2^256) :
    (sub senderBal amount).toNat + (add receiverBal amount).toNat =
    senderBal.toNat + receiverBal.toNat := by
  simp [sub, add, BitVec.toNat_sub, BitVec.toNat_add]
  omega

/-- Storage non-interference for balance updates. -/
theorem balance_slot_frame (storage : EVMStorage) (addr other : Word256)
    (v : Word256) (hNe : (balanceSlot addr == balanceSlot other) = false) :
    (storage.sstore (balanceSlot other) v).sload (balanceSlot addr) =
    storage.sload (balanceSlot addr) :=
  EVMStorage.sload_sstore_ne storage (balanceSlot addr) (balanceSlot other) v hNe

/-- Storage update for the written slot. -/
theorem balance_slot_update (storage : EVMStorage) (addr v : Word256) :
    (storage.sstore (balanceSlot addr) v).sload (balanceSlot addr) = v :=
  EVMStorage.sload_sstore_same storage (balanceSlot addr) v

/-- Transfer non-interference: a transfer between sender and receiver
    does not affect the balance of any third party. -/
theorem balance_transfer_noninterference (storage : EVMStorage)
    (sender receiver other newSenderBal newReceiverBal : Word256)
    (hNeSender : (balanceSlot other == balanceSlot sender) = false)
    (hNeReceiver : (balanceSlot other == balanceSlot receiver) = false) :
    let s1 := storage.sstore (balanceSlot sender) newSenderBal
    let s2 := s1.sstore (balanceSlot receiver) newReceiverBal
    s2.sload (balanceSlot other) = storage.sload (balanceSlot other) := by
  simp only
  rw [EVMStorage.sload_sstore_ne _ _ _ _ hNeReceiver]
  rw [EVMStorage.sload_sstore_ne _ _ _ _ hNeSender]

end LeanSP.RealWorld
