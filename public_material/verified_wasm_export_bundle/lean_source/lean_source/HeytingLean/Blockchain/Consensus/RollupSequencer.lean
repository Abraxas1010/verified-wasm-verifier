import HeytingLean.Blockchain.Consensus.RollupDataAvailability
import HeytingLean.Blockchain.Rollup.Model

/-
# Consensus.RollupSequencer

Semantic target for `Consensus.Spec.PropertyId.sequencerCorrectness`,
expressed in terms of a simple sequencer schedule over rollup
transactions.

We model a sequencer as a function `sched : Time → List Tx` that
produces, at each discrete slot, a batch of transactions. For any
finite horizon `T`, this induces a list of batches obtained from
`List.range T`. Sequencer correctness is then captured by the property
that executing these batches slot-by-slot yields the same rollup state
as executing the concatenation of all scheduled transactions, reusing
the underlying data-availability lemma.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace RollupSequencer

open HeytingLean.Blockchain
open HeytingLean.Blockchain.Rollup
open RollupDataAvailability

/-- Discrete time index for the sequencer schedule. For this minimal
    model we take it to be natural numbers. -/
abbrev Time := Nat

/-- Turn a time-indexed sequencer schedule into a finite list of
    transaction batches by sampling it on `List.range T`. -/
def scheduleToBatches (sched : Time → List Tx) (T : Nat) :
    List (List Tx) :=
  (List.range T).map sched

/-- Semantic statement for `PropertyId.sequencerCorrectness`.

For any initial rollup state `s₀`, sequencer schedule `sched`, and
finite horizon `T`, executing the batches produced by `sched` up to
time `T` one-by-one yields the same state as executing the
concatenation of all scheduled transactions. -/
def Statement : Prop :=
  ∀ (s₀ : State) (sched : Time → List Tx) (T : Nat),
    let batches := scheduleToBatches sched T
    applyTxs s₀ (flattenBatches batches) =
      List.foldl (fun st txs => applyTxs st txs) s₀ batches

/-- `Statement` holds by instantiating the rollup data-availability
    theorem with the batches induced by the sequencer schedule. -/
theorem statement_holds : Statement := by
  intro s₀ sched T
  -- Instantiate `RollupDataAvailability.statement_holds` with the
  -- batches produced by the schedule up to time `T`.
  let batches := scheduleToBatches sched T
  have h :=
    RollupDataAvailability.statement_holds
      (s₀ := s₀) (batches := batches)
  simpa [scheduleToBatches] using h

end RollupSequencer
end Consensus
end Blockchain
end HeytingLean
