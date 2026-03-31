import HeytingLean.Blockchain.Consensus.Core

/-
# Consensus.LivenessExample

A minimal example liveness instance on top of the consensus core model,
intended to mirror the shape of chain-growth-style properties without
yet committing to a full probabilistic or adversarial model.

We define:
* a simple "ever-growing" execution where all honest nodes see chains
  whose lengths coincide with the time index; and
* a chain-growth-style property requiring that chain lengths are
  monotone in time, and prove it for this execution.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace LivenessExample

open Core

/-- A chain-growth-style predicate specialised to the simplified
    length-based `ChainGrowth` predicate from the core model. This
    alias makes it clear that the example instance is exercising the same
    notion of chain growth that `Core.propertyHolds` uses for the
    `chainGrowth` registry row. -/
def ChainGrowthExample (exec : Execution) : Prop :=
  Core.ChainGrowth exec

/-- A chain-quality-style predicate specialised to the simplified
    length-based `ChainQuality` predicate from the core model. -/
def ChainQualityExample (exec : Execution) : Prop :=
  Core.ChainQuality exec

/-- A no-double-spending-style predicate specialised to the core
    `NoDoubleSpending` predicate. -/
def NoDoubleSpendingExample (exec : Execution) : Prop :=
  Core.NoDoubleSpending exec

/-- A finality-style predicate specialised to the core `Finality`
    predicate. -/
def FinalityExample (exec : Execution) : Prop :=
  Core.Finality exec

/-- A slashing-correctness-style predicate specialised to the core
    `SlashingCorrectness` predicate. -/
def SlashingCorrectnessExample (exec : Execution) : Prop :=
  Core.SlashingCorrectness exec

/-- An example execution in which every honest node's chain at time `t` is
    exactly the list `[0, 1, ..., t - 1]`. In this model, chains grow
    by one block per time step for all nodes. -/
def growingExecution : Execution :=
  { chainAt := fun t _ => List.range t
    , honest := fun _ => True }

/-- In the example execution, all honest nodes see the same chain at each
    time, so the no-fork predicate holds. -/
theorem growingExecution_noFork :
    Core.NoFork growingExecution := by
  -- Use the generic equal-chain lemma with `f t := List.range t`.
  refine Core.NoFork_of_eq_chainAt growingExecution (fun t => List.range t) ?h
  intro t n _
  simp [growingExecution]

/-- In the example execution, no honest chain ever contains duplicate block
    identifiers: each chain is `List.range t`, which is duplicate-free. -/
theorem growingExecution_noDoubleSpending :
    NoDoubleSpendingExample growingExecution := by
  intro t n _
  simp [growingExecution, List.nodup_range]

/-- `growingExecution` satisfies the `ChainGrowthExample` property: chain
    lengths coincide with the time index and are therefore monotone in
    time. -/
theorem growingExecution_chainGrowth :
    ChainGrowthExample growingExecution := by
  -- Chains are `List.range t`, so their lengths are exactly the time index.
  intro t₁ t₂ _ _ hle
  simp [growingExecution] at *
  exact hle

/-- `growingExecution` also satisfies the `ChainQualityExample` property:
    the chain length at time `t` is exactly `t`, so it is in particular
    at least `t / 2`. -/
theorem growingExecution_chainQuality :
    ChainQualityExample growingExecution := by
  intro t _ _
  simp [growingExecution]
  -- We use `Nat.div_le_self` with denominator `2` to show `t / 2 ≤ t`.
  simpa using Nat.div_le_self t 2

/-- `growingExecution` also satisfies a `k`‑deep finality property for
    `k = 0`: once a block appears in an honest node's chain at some
    time, it remains in that node's chain at all later times. -/
theorem growingExecution_kFinality_zero :
    Core.KFinality 0 growingExecution := by
  intro t₀ t₁ n b _ hLe hMem _
  -- Membership in `List.range t₀` is equivalent to `b < t₀`.
  have hb_lt : b < t₀ := by
    simpa [growingExecution] using hMem
  -- Monotonicity of `<` in the second argument.
  have hb_lt' : b < t₁ := Nat.lt_of_lt_of_le hb_lt hLe
  -- Repackage as membership in `List.range t₁`.
  simpa [growingExecution] using hb_lt'

/-- `growingExecution` satisfies the (existential) finality predicate
    by taking the witness `k = 0`. -/
theorem growingExecution_finality :
    FinalityExample growingExecution := by
  refine ⟨0, ?_⟩
  exact growingExecution_kFinality_zero

/-- `growingExecution` satisfies the slashing-correctness predicate:
    it has no forks and no double-spending. -/
theorem growingExecution_slashingCorrectness :
    SlashingCorrectnessExample growingExecution := by
  refine And.intro ?hNoFork ?hNoDouble
  · -- No-fork via the equal-chain lemma.
    exact growingExecution_noFork
  · -- No double-spending via `List.nodup_range`.
    exact growingExecution_noDoubleSpending

/-- `growingExecution` satisfies the transaction-inclusion property:
    any block that appears in the chain of an honest node at some time
    is already present in the chains of all honest nodes at that time,
    since all chains are definitionally equal. -/
theorem growingExecution_txInclusion :
    Core.TxInclusion growingExecution := by
  intro t₀ n₀ _ b hb
  refine ⟨t₀, Nat.le_refl _, ?_⟩
  intro n _
  -- Chains do not depend on the node, so membership is shared.
  simpa [growingExecution] using hb

/-- Registry-level chain-growth instance for the example execution:
    the `Consensus.Spec.PropertyId.chainGrowth` predicate holds for
    `growingExecution` via the core `ChainGrowth` predicate. -/
theorem propertyHolds_chainGrowth_growingExecution :
    Core.propertyHolds growingExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.chainGrowth := by
  have h : Core.ChainGrowth growingExecution :=
    growingExecution_chainGrowth
  simpa [Core.propertyHolds, ChainGrowthExample] using h

/-- Registry-level chain-quality instance for the example execution:
    the `Consensus.Spec.PropertyId.chainQuality` predicate holds for
    `growingExecution` via the core `ChainQuality` predicate. -/
theorem propertyHolds_chainQuality_growingExecution :
    Core.propertyHolds growingExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.chainQuality := by
  have h : Core.ChainQuality growingExecution :=
    growingExecution_chainQuality
  simpa [Core.propertyHolds, ChainQualityExample] using h

/-- Registry-level transaction-inclusion instance for the example
    execution: the `Consensus.Spec.PropertyId.transactionInclusion`
    predicate holds for `growingExecution` via the core `TxInclusion`
    predicate. -/
theorem propertyHolds_transactionInclusion_growingExecution :
    Core.propertyHolds growingExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.transactionInclusion := by
  have h : Core.TxInclusion growingExecution :=
    growingExecution_txInclusion
  simpa [Core.propertyHolds] using h

/-- Registry-level leader-election fairness instance for the example
    execution: with the trivial schedule `L t := t`, every honest node
    (here, every node) is scheduled at least once. -/
theorem propertyHolds_leaderElectionFairness_growingExecution :
    Core.propertyHolds growingExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.leaderElectionFairness := by
  -- Define the simple leader schedule.
  let L : Time → NodeId := fun t => t
  have hFair : Core.LeaderElectionFairness growingExecution := by
    refine ⟨L, ?_, ?_⟩
    · intro t
      -- All nodes are honest in `growingExecution`.
      simp [L, growingExecution]
    · intro n _
      -- Node `n` is scheduled at time `n`.
      refine ⟨n, ?_⟩
      simp [L]
  simpa [Core.propertyHolds] using hFair

/-- Registry-level no-double-spending instance for the example execution:
    the `Consensus.Spec.PropertyId.noDoubleSpending` predicate holds
    for `growingExecution` via the core `NoDoubleSpending` predicate. -/
theorem propertyHolds_noDoubleSpending_growingExecution :
    Core.propertyHolds growingExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.noDoubleSpending := by
  have h : Core.NoDoubleSpending growingExecution :=
    growingExecution_noDoubleSpending
  simpa [Core.propertyHolds, NoDoubleSpendingExample] using h

/-- Registry-level finality instance for the example execution: the
    `Consensus.Spec.PropertyId.finalityGuarantee` predicate holds for
    `growingExecution` via the core `Finality` predicate. -/
theorem propertyHolds_finality_growingExecution :
    Core.propertyHolds growingExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.finalityGuarantee := by
  have h : FinalityExample growingExecution :=
    growingExecution_finality
  simpa [Core.propertyHolds, FinalityExample] using h

/-- Registry-level slashing-correctness instance for the example execution:
    the `Consensus.Spec.PropertyId.slashingCorrectness` predicate holds
    for `growingExecution` via the core `SlashingCorrectness` predicate. -/
theorem propertyHolds_slashingCorrectness_growingExecution :
    Core.propertyHolds growingExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.slashingCorrectness := by
  have h : SlashingCorrectnessExample growingExecution :=
    growingExecution_slashingCorrectness
  simpa [Core.propertyHolds, SlashingCorrectnessExample] using h

end LivenessExample
end Consensus
end Blockchain
end HeytingLean
