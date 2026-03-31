import Lean
import HeytingLean.Blockchain.Consensus.Core
import HeytingLean.Blockchain.Consensus.Spec
import HeytingLean.Blockchain.Consensus.LongestChain
import HeytingLean.Blockchain.Consensus.LivenessExample

/-
# consensus_demo CLI

Lightweight CLI intended to exercise the consensus core predicates
defined in `Blockchain.Consensus.Core`. For now it constructs a trivial
execution and reports whether a few core properties hold. As the safety
and liveness theorems are developed, this CLI can be extended to run
small protocol simulations.
-/

namespace HeytingLean
namespace CLI
namespace ConsensusDemo

open HeytingLean.Blockchain.Consensus
open HeytingLean.Blockchain.Consensus.Core
open HeytingLean.Blockchain.Consensus.LongestChain
open HeytingLean.Blockchain.Consensus.LivenessExample

/-- A tiny equal-chain example execution with all nodes sharing the
    empty chain. -/
def equalExecution : Execution :=
  { chainAt := fun _ _ => []
    , honest := fun _ => True }

/-- For `equalExecution`, all honest nodes see the same chain at each
    time, so `NoFork` holds by `NoFork_of_eq_chainAt`. -/
theorem equalExecution_noFork : NoFork equalExecution := by
  apply NoFork_of_eq_chainAt (exec := equalExecution) (f := fun _ => [])
  intro t n hn
  simp [equalExecution]

/-- For `equalExecution`, all honest nodes see the same chain at each
    time, so `CommonPrefix k` holds for every `k`. -/
theorem equalExecution_commonPrefix (k : Nat) :
    CommonPrefix k equalExecution := by
  apply CommonPrefix_of_eq_chainAt (exec := equalExecution) (f := fun _ => [])
  intro t n hn
  simp [equalExecution]

/-- A simple canonical chain used for the longest-chain example. -/
def longestCanonical : Time → Core.Chain :=
  fun _ => [0, 1, 2]

/-- A longest-chain-style execution where honest nodes may hold
    different prefixes of a fixed canonical chain. -/
def longestExecution : Execution :=
  { chainAt := fun _ n =>
      if n = 0 then [0, 1, 2]
      else if n = 1 then [0, 1]
      else if n = 2 then [0]
      else []
    , honest := fun _ => True }

/-- Every honest node's chain in `longestExecution` is a prefix of the
    canonical chain `longestCanonical t`. -/
theorem longestExecution_prefix
    (t : Time) (n : NodeId) (hn : longestExecution.honest n) :
    Core.isPrefix (longestExecution.chainAt t n) (longestCanonical t) := by
  classical
  unfold longestExecution longestCanonical at *
  by_cases h0 : n = 0
  · subst h0
    -- Full canonical chain: `[0, 1, 2]` is a prefix of itself.
    refine ⟨[], ?_⟩
    simp
  · by_cases h1 : n = 1
    · subst h1
      -- `[0, 1]` is a prefix of `[0, 1, 2]`.
      refine ⟨[2], ?_⟩
      simp
    · by_cases h2 : n = 2
      · subst h2
        -- `[0]` is a prefix of `[0, 1, 2]`.
        refine ⟨[1, 2], ?_⟩
        simp
      · -- All other nodes see the empty chain, which is a prefix of any chain.
        refine ⟨[0, 1, 2], ?_⟩
        simp [h0, h1, h2]

/-- For `longestExecution`, the longest-chain assumption holds with
    `longestCanonical`, so `NoFork` follows from `noFork_longestChain`. -/
theorem longestExecution_noFork : NoFork longestExecution :=
  noFork_longestChain longestExecution longestCanonical longestExecution_prefix

/-- For `longestExecution`, the longest-chain assumption also yields
    `CommonPrefix k` for every `k`. -/
theorem longestExecution_commonPrefix (k : Nat) :
    CommonPrefix k longestExecution :=
  commonPrefix_longestChain k longestExecution longestCanonical longestExecution_prefix

def main (_argv : List String) : IO UInt32 := do
  -- Equal-chain instance exercised via `equalExecution_*` theorems.
  IO.println "consensus_demo (equal-chains): noFork=true, commonPrefix=true"
  -- Longest-chain instance exercised via `longestExecution_*` theorems.
  IO.println "consensus_demo (longest-chain): noFork=true, commonPrefix=true"
  -- Growing-execution liveness instance from `Consensus.LivenessExample`:
  -- chain growth, chain quality, transaction inclusion, and
  -- leader-election fairness are all witnessed by the corresponding
  -- theorems in that module.
  IO.println "consensus_demo (growing-execution): chainGrowth=true, chainQuality=true, txInclusion=true, leaderElectionFairness=true"
  pure 0

end ConsensusDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ConsensusDemo.main args
