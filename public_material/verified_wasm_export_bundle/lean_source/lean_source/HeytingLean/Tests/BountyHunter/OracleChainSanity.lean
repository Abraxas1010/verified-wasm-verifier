import HeytingLean.BountyHunter.Foundry.OracleChain

namespace HeytingLean.Tests.BountyHunter

open HeytingLean.BountyHunter.Foundry.OracleChain
open HeytingLean.Core

def transferCtx : ExecutionContext :=
  { fn := { signature := "transfer(address,uint256)" }
    calldata := []
    msgValue := 0 }

def transferOk : OkRevertParityWitness :=
  mkOkRevertParityWitness transferCtx true true rfl

def transferReturn : ReturnBytesParityWitness :=
  mkReturnBytesParityWitness transferOk ⟨rfl, rfl⟩

def transferEvent : EventLogParityWitness :=
  mkEventLogParityWitness transferReturn 2

def transferStorage : StorageParityWitness :=
  mkStorageParityWitness transferEvent 4

local instance : IsWitnessStep (IsWitnessStep.Upstream (W := StorageParityWitness)) where
  Upstream := ReturnBytesParityWitness
  upstream w := w.sourceReturnBytes

example : transferOk.ctx.fn.signature = "transfer(address,uint256)" := by
  rfl

example : ∃ w : FullParityWitness, w.fn.signature = "transfer(address,uint256)" := by
  rcases parity_gen_correspondence transferCtx true true rfl rfl with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  simpa [transferCtx] using congrArg CheckedFunction.signature hw

example :
    ∃ (w3 : EventLogParityWitness) (w2 : ReturnBytesParityWitness)
      (w1 : OkRevertParityWitness),
      transferStorage.sourceEventLog = w3 ∧
        w3.sourceReturnBytes = w2 ∧
        w2.sourceOkRevert = w1 := by
  exact storage_implies_full_chain transferStorage

example :
    ∃ w3 : EventLogParityWitness, IsWitnessStep.upstream transferStorage = w3 := by
  exact upstream_exists transferStorage

example :
    ∃ w2 : ReturnBytesParityWitness, upstream2 transferStorage = w2 := by
  exact upstream2_exists transferStorage

example :
    chain_requires_all_steps
      { storage := transferStorage
        fn := transferCtx.fn
        fn_eq := rfl } = rfl := by
  rfl

end HeytingLean.Tests.BountyHunter
