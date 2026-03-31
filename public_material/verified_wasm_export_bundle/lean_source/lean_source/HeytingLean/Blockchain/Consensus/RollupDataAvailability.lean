import HeytingLean.Blockchain.Rollup.Model
import HeytingLean.Blockchain.Consensus.Spec

/-
# Consensus.RollupDataAvailability

Semantic target for `Consensus.Spec.PropertyId.dataAvailability`,
grounded in the concrete rollup model from `Blockchain.Rollup.Model`.

The statement captures a simple but robust notion of data availability:
executing a sequence of transaction *batches* is equivalent (at the
accounts level) to executing the flattened list of all transactions in
order. In other words, given access to all batch data, the final
rollup state is determined solely by the concatenated transaction list.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace RollupDataAvailability

open HeytingLean.Blockchain.Rollup

/-- Flatten a list of transaction batches into a single transaction
    list by concatenation. -/
def flattenBatches (batches : List (List Tx)) : List Tx :=
  batches.foldr List.append []

/-- Semantic statement for `PropertyId.dataAvailability` in the rollup
    model: for any initial state `s₀` and list of batches of
    transactions, applying the batches one by one is equivalent to
    applying the concatenation of all transactions in order. -/
def Statement : Prop :=
  ∀ (s₀ : State) (batches : List (List Tx)),
    applyTxs s₀ (flattenBatches batches) =
      List.foldl (fun st txs => applyTxs st txs) s₀ batches

/-- `Statement` holds, by induction on the list of batches and the
    composition law `applyTxs_append`. -/
theorem statement_holds : Statement := by
  intro s₀ batches
  induction batches generalizing s₀ with
  | nil =>
      -- No batches: both sides leave the state unchanged.
      simp [flattenBatches, applyTxs, List.foldl]
  | cons batch batches ih =>
      -- Expand the goal for `batch :: batches` and rewrite both sides.
      have hLeft :
          applyTxs s₀ (flattenBatches (batch :: batches)) =
            applyTxs (applyTxs s₀ batch) (flattenBatches batches) := by
        -- `flattenBatches (batch :: batches)` is `batch ++ flattenBatches batches`.
        simp [flattenBatches, applyTxs_append]
      have hRight :
          List.foldl (fun st txs => applyTxs st txs) s₀ (batch :: batches) =
            List.foldl (fun st txs => applyTxs st txs)
              (applyTxs s₀ batch) batches := by
        simp [List.foldl]
      -- Instantiate the induction hypothesis at `applyTxs s₀ batch`.
      have hIH :
          applyTxs (applyTxs s₀ batch) (flattenBatches batches) =
            List.foldl (fun st txs => applyTxs st txs)
              (applyTxs s₀ batch) batches :=
        ih (applyTxs s₀ batch)
      -- Chain the equalities.
      exact (hLeft.trans hIH).trans hRight.symm

end RollupDataAvailability
end Consensus
end Blockchain
end HeytingLean
