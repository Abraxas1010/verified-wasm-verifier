import Lean
import HeytingLean.Blockchain.Rollup.Model

/-
# rollup_demo CLI

Small CLI that exercises the concrete rollup model by:

* constructing a tiny initial state and transaction batch;
* computing the `k`-step iterated state `stateAfterSteps s₀ txs k`;
* computing the closed-form big-batch state `bigBatchState s₀ txs k`;
* printing both states so their equality (guaranteed by the theorem
  `stateAfterSteps_eq_bigBatch`) can be inspected at runtime.

This CLI acts as an executable harness for the rollup state-root
validity statement used in the consensus registry.
-/

namespace HeytingLean
namespace CLI
namespace RollupDemo

open HeytingLean.Blockchain.Rollup

/-- A tiny initial rollup state with two accounts. -/
def exampleState : State :=
  { accounts :=
      [ { addr := 1, balance := 10, nonce := 0 }
        , { addr := 2, balance := 0, nonce := 0 } ]
    commit := "init" }

/-- A simple transfer transaction from account 1 to account 2. -/
def exampleTxs : List Tx :=
  [ { fromAddr := 1, toAddr := 2, amount := 3 } ]

/-- Main entry point: run a small rollup example for `k` batches and
    print both the iterated and big-batch states. -/
def main (args : List String) : IO UInt32 := do
  let k : Nat :=
    match args.headD "2" |>.toNat? with
    | some n => n
    | none   => 2
  let s₀ := exampleState
  let txs := exampleTxs
  let sIter := stateAfterSteps s₀ txs k
  let sBatch := bigBatchState s₀ txs k
  IO.println s!"rollup_demo: k = {k}"
  IO.println "  initial accounts:"
  IO.println s!"    count = {s₀.accounts.length}"
  IO.println "  tx batch:"
  IO.println s!"    count = {txs.length}"
  IO.println "  iterated state:"
  IO.println s!"    commit = {sIter.commit}"
  IO.println "  big-batch state:"
  IO.println s!"    commit = {sBatch.commit}"
  pure 0

end RollupDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.RollupDemo.main args
