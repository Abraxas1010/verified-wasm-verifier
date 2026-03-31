import HeytingLean.Blockchain.Rollup.Model
import HeytingLean.Blockchain.Consensus.Spec

/-
# Consensus.RollupStateRoot

Semantic target for `Consensus.Spec.PropertyId.stateRootValidity`,
grounded in the concrete rollup model from `Blockchain.Rollup.Model`.

The key idea is that iterating the one-step rollup transition `k` times
from an initial state `s₀` yields the same state (including the state
commitment) as applying the batch of transactions corresponding to
those `k` steps once and recomputing the commitment. This is captured
by `Rollup.stateAfterSteps_eq_bigBatch`, which we package here as a
registry-friendly `Statement`.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace RollupStateRoot

open HeytingLean.LoF
open HeytingLean.Blockchain.Rollup

variable {α : Type} [PrimaryAlgebra α]
variable {R : Reentry α}

/-- Semantic statement for `PropertyId.stateRootValidity`:

For any initial rollup state `s₀`, transaction list `txs`, and number
of batches `k`, the iterated rollup state obtained by applying the
concrete step `k` times coincides with the “big-batch” state obtained
by applying `txs` `k` times in one go and recomputing the commitment. -/
def Statement : Prop :=
  ∀ (s₀ : State) (txs : List Tx) (k : Nat),
    stateAfterSteps s₀ txs k =
      bigBatchState s₀ txs k

/-- `Statement` holds, witnessed directly by
`stateAfterSteps_eq_bigBatch` from the rollup model. -/
theorem statement_holds : Statement := by
  intro s₀ txs k
  simpa using
    stateAfterSteps_eq_bigBatch s₀ txs k

end RollupStateRoot
end Consensus
end Blockchain
end HeytingLean
