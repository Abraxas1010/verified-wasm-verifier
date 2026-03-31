import HeytingLean.Blockchain.Consensus.Spec
import HeytingLean.Blockchain.Consensus.MerkleProof
import HeytingLean.Blockchain.Consensus.LightClient
import HeytingLean.Blockchain.Consensus.RollupStateRoot
import HeytingLean.Blockchain.Consensus.RollupDataAvailability
import HeytingLean.Blockchain.Consensus.RollupSequencer
import HeytingLean.Blockchain.Consensus.RollupEscapeHatch
import HeytingLean.Blockchain.Consensus.MessagePassing
import HeytingLean.Blockchain.Consensus.LockedValue
import HeytingLean.Blockchain.Consensus.MerklePatriciaTrie
import HeytingLean.Blockchain.Consensus.ValidatorTransitions
import HeytingLean.Blockchain.Consensus.StatePruning
import HeytingLean.Blockchain.Consensus.DatabaseConsistency
import HeytingLean.Blockchain.Consensus.MerklePatriciaTrie

/-
# Blockchain.Consensus.Core

Minimal consensus core model providing:

* abstract blocks, chains, and executions;
* generic safety/liveness predicates (no fork, common prefix, etc.);
* an assumption bundle for adversary/synchrony/leader-election; and
* statement types tying these predicates to the registry in
  `Blockchain.Consensus.Spec`.

This file focuses on stable *types* and predicate names. It intentionally
avoids deep proofs so that later safety/liveness developments can depend
on a fixed API without introducing proof holes here.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace Core

open HeytingLean.Blockchain

/-- Abstract identifier for nodes. -/
abbrev NodeId := Nat

/-- Abstract identifier for blocks. -/
abbrev BlockId := Nat

/-- A chain is a list of block identifiers, with the head of the list
    representing the most recent block. -/
abbrev Chain := List BlockId

/-- Discrete time index (slots / rounds). -/
abbrev Time := Nat

/-- Prefix relation between chains: `c₁` is a (suffix-normalised) prefix
    of `c₂` if `c₂ = c₁ ++ suffix` for some suffix. -/
def isPrefix (c₁ c₂ : Chain) : Prop :=
  ∃ suffix : Chain, c₂ = c₁ ++ suffix

/-- Reflexivity of the prefix relation. -/
@[simp] theorem isPrefix_refl (c : Chain) : isPrefix c c :=
  ⟨[], by simp⟩

/-- The empty chain is a prefix of any chain. -/
theorem isPrefix_nil (c : Chain) : isPrefix [] c :=
  ⟨c, by simp⟩

/-- Execution model: for each time and node, we have a current chain,
    and a predicate marking honest nodes. -/
structure Execution where
  chainAt : Time → NodeId → Chain
  honest  : NodeId → Prop

/-- Safety: at every time, the chains held by any two honest nodes are
    comparable by the prefix relation (no conflicting histories). -/
def NoFork (exec : Execution) : Prop :=
  ∀ (t : Time) (n₁ n₂ : NodeId),
    exec.honest n₁ → exec.honest n₂ →
      isPrefix (exec.chainAt t n₁) (exec.chainAt t n₂) ∨
      isPrefix (exec.chainAt t n₂) (exec.chainAt t n₁)

/-- If all honest nodes see the same chain at each time, then `NoFork`
    holds: honest chains are trivially comparable by equality. -/
theorem NoFork_of_eq_chainAt (exec : Execution)
    (f : Time → Chain)
    (h : ∀ (t : Time) (n : NodeId),
      exec.honest n → exec.chainAt t n = f t) :
    NoFork exec := by
  intro t n₁ n₂ h₁ h₂
  have h₁' : exec.chainAt t n₁ = f t := h t n₁ h₁
  have h₂' : exec.chainAt t n₂ = f t := h t n₂ h₂
  -- Both chains agree with `f t`, so are equal; reflexivity of
  -- `isPrefix` yields comparability.
  refine Or.inl ?_
  -- Rewrite the goal to `isPrefix (f t) (f t)` and apply reflexivity.
  simp [h₁', h₂', isPrefix_refl]

/-- Common-prefix-style property (blueprint-level).

For a given parameter `k`, we require that at any time and for any two
honest nodes, their chains share a large common prefix. This is stated
abstractly here; concrete developments can impose stronger numeric
conditions on the shared prefix. -/
def CommonPrefix (_k : Nat) (exec : Execution) : Prop :=
  ∀ (t : Time) (n₁ n₂ : NodeId),
    exec.honest n₁ → exec.honest n₂ →
      ∃ c : Chain,
        isPrefix c (exec.chainAt t n₁) ∧
        isPrefix c (exec.chainAt t n₂)

/-- If all honest nodes see the same chain at each time, then they share
    a common prefix at every time: namely that chain. The parameter `k`
    is currently a blueprint index and does not constrain the prefix
    length in this simplified model. -/
theorem CommonPrefix_of_eq_chainAt (k : Nat) (exec : Execution)
    (f : Time → Chain)
    (h : ∀ (t : Time) (n : NodeId),
      exec.honest n → exec.chainAt t n = f t) :
    CommonPrefix k exec := by
  intro t n₁ n₂ h₁ h₂
  have h₁' : exec.chainAt t n₁ = f t := h t n₁ h₁
  have h₂' : exec.chainAt t n₂ = f t := h t n₂ h₂
  refine ⟨f t, ?_⟩
  constructor
  · -- `f t` is a prefix of the chain at `n₁`.
    simp [h₁', isPrefix_refl]
  · -- `f t` is also a prefix of the chain at `n₂`.
    simp [h₂', isPrefix_refl]

/-- Core no-fork theorem under a global equal-chain condition:
    whenever there exists a function `f` such that all honest nodes see
    `f t` at every time `t`, the execution satisfies `NoFork`. This
    provides a concrete realisation of the semantic shape behind
    `Consensus.Spec.PropertyId.noForkTheorem` at the core-model level. -/
theorem noForkTheorem_equalChains
    (exec : Execution) (f : Time → Chain)
    (h : ∀ (t : Time) (n : NodeId),
      exec.honest n → exec.chainAt t n = f t) :
    NoFork exec :=
  NoFork_of_eq_chainAt exec f h

/-- Core common-prefix theorem under a global equal-chain condition:
    whenever there exists a function `f` such that all honest nodes see
    `f t` at every time `t`, the execution satisfies `CommonPrefix k`
    for every `k`. This matches the intended semantic target of
    `Consensus.Spec.PropertyId.commonPrefixProperty` in the simplest
    “all chains equal” regime. -/
theorem commonPrefixTheorem_equalChains
    (k : Nat) (exec : Execution) (f : Time → Chain)
    (h : ∀ (t : Time) (n : NodeId),
      exec.honest n → exec.chainAt t n = f t) :
    CommonPrefix k exec :=
  CommonPrefix_of_eq_chainAt k exec f h

/-! ## Nontrivial witnesses (anti-vacuity) -/

/-- A concrete execution with at least one honest node (node `0`), whose
honest view is driven by a single global chain function `f`. This is a
small witness used to preempt “vacuity” concerns in simplified models. -/
def exampleExecution (f : Time → Chain) : Execution :=
  { chainAt := fun t n => if n = 0 then f t else []
    honest := fun n => n = 0 }

@[simp] lemma exampleExecution_honest_iff (f : Time → Chain) (n : NodeId) :
    (exampleExecution f).honest n ↔ n = 0 := Iff.rfl

@[simp] lemma exampleExecution_chainAt_zero (f : Time → Chain) (t : Time) :
    (exampleExecution f).chainAt t 0 = f t := by
  simp [exampleExecution]

theorem exampleExecution_noFork (f : Time → Chain) :
    NoFork (exampleExecution f) := by
  refine noForkTheorem_equalChains (exec := exampleExecution f) (f := f) ?_
  intro t n hn
  have hn0 : n = 0 := hn
  simp [exampleExecution, hn0]

theorem exampleExecution_nontrivial_witness :
    ∃ exec : Execution,
      exec.honest 0 ∧ exec.chainAt 0 0 ≠ [] ∧ NoFork exec := by
  let f : Time → Chain := fun _ => [0]
  refine ⟨exampleExecution f, ?_, ?_, ?_⟩
  · simp [exampleExecution]
  · simp [exampleExecution, f]
  · simpa [f] using exampleExecution_noFork (f := f)

/-- Chain-growth-style property: along any honest node's view, the
    length of its chain is monotone in time. This is a simplified,
    length-based analogue of standard chain-growth properties; later
    developments can refine it with windowed growth bounds and
    probabilistic assumptions. -/
def ChainGrowth (exec : Execution) : Prop :=
  ∀ (t₁ t₂ : Time) (n : NodeId),
    exec.honest n →
    t₁ ≤ t₂ →
    (exec.chainAt t₁ n).length ≤ (exec.chainAt t₂ n).length

/-- Chain-quality-style property: for each time and honest node, the
    chain length is bounded below by a simple linear function of time.
    In this initial model we require that the length at time `t` is at
    least `t / 2`; later developments can refine this into a genuine
    lower bound on *honest* blocks using explicit block labellings and
    probabilistic assumptions. -/
def ChainQuality (exec : Execution) : Prop :=
  ∀ (t : Time) (n : NodeId),
    exec.honest n →
    (exec.chainAt t n).length ≥ t / 2

/-- Transaction-inclusion-style property: any block that appears in the
    chain of an honest node at some time is eventually present in the
    chains of all honest nodes (possibly immediately). This is a
    simplified eventual-inclusion property phrased purely in terms of
    block identifiers and chains. -/
def TxInclusion (exec : Execution) : Prop :=
  ∀ (t₀ : Time) (n₀ : NodeId),
    exec.honest n₀ →
    ∀ b, b ∈ exec.chainAt t₀ n₀ →
      ∃ t₁ : Time, t₀ ≤ t₁ ∧
        ∀ n : NodeId, exec.honest n → b ∈ exec.chainAt t₁ n

/-- Leader-election-fairness-style property: there exists a leader
    schedule that only selects honest nodes, and every honest node is
    scheduled at least once. This is a deliberately simple, one-shot
    fairness property suitable for example executions; later developments
    can strengthen it to long-run frequency bounds. -/
def LeaderElectionFairness (exec : Execution) : Prop :=
  ∃ L : Time → NodeId,
    (∀ t, exec.honest (L t)) ∧
    ∀ n : NodeId, exec.honest n → ∃ t : Time, L t = n

/-- Gossip-protocol-style safety property: at each time, all honest
    nodes see the same chain. This rules out inconsistent views arising
    purely from the gossip layer. -/
def GossipProtocolSafety (exec : Execution) : Prop :=
  ∀ t n₁ n₂,
    exec.honest n₁ → exec.honest n₂ →
      exec.chainAt t n₁ = exec.chainAt t n₂

/-- Eclipse-attack-resistance-style property: honest nodes are never
    fully isolated in the sense of having an empty chain. This is a
    very simple safety condition stating that honest nodes always see at
    least a genesis block. -/
def EclipseAttackResistance (exec : Execution) : Prop :=
  ∀ t n,
    exec.honest n →
      exec.chainAt t n ≠ []

/-- No-double-spending-style property: for every time and honest node,
    the block identifiers in its chain are pairwise distinct. In this
    minimal model, this prevents reusing the same block identifier
    twice in a single honest chain. -/
def NoDoubleSpending (exec : Execution) : Prop :=
  ∀ t n, exec.honest n → (exec.chainAt t n).Nodup

/-- DoS-resistance-style property: honest nodes cannot be overloaded by
    unbounded chain growth. In this example model we require that the chain
    length for any honest node at time `t` is bounded by `t + 1`, which
    can be read as a crude per-slot rate limit. -/
def DosResistance (exec : Execution) : Prop :=
  ∀ t n,
    exec.honest n →
      (exec.chainAt t n).length ≤ t + 1

/-- `k`‑deep finality-style property: once a block appears in an honest
    node’s chain at some time with chain length at least `k`, it remains
    present in that node’s chain at all later times. In a more detailed
    model, the length guard would be replaced by an explicit depth check;
    here it serves as a simple proxy for “far enough from the tip”. -/
def KFinality (k : Nat) (exec : Execution) : Prop :=
  ∀ (t₀ t₁ : Time) (n : NodeId) (b : BlockId),
    exec.honest n →
    t₀ ≤ t₁ →
    b ∈ exec.chainAt t₀ n →
    (exec.chainAt t₀ n).length ≥ k →
    b ∈ exec.chainAt t₁ n

/-- Finality-style property: there exists some `k` such that the
    `k`‑deep finality condition holds. Concrete protocol instances are
    expected to provide bounds on such a `k`. -/
def Finality (exec : Execution) : Prop :=
  ∃ k, KFinality k exec

/-- Slashing-correctness-style property: no slashing-relevant safety
    violation occurs. At this abstraction level we model it as the
    conjunction of the no-fork and no-double-spending predicates. -/
def SlashingCorrectness (exec : Execution) : Prop :=
  NoFork exec ∧ NoDoubleSpending exec

/-- Assumption bundle capturing adversary fraction, synchrony, and
    leader-election properties in an abstract form. Specific models
    (PoS-NSB, Ouroboros, PBFT, etc.) will specialise this. -/
structure Assumptions where
  adversaryBounds : Prop
  synchrony       : Prop
  leaderElection  : Prop

/-- Core no-fork statement type: under a given assumption bundle and
    execution-model assumptions, the `NoFork` predicate holds. Concrete
    developments will instantiate this with precise hypotheses. -/
def NoForkStatement (A : Assumptions) : Prop :=
  ∀ exec : Execution, A.adversaryBounds → A.synchrony → NoFork exec

/-- Core common-prefix statement type (indexed by `k`). -/
def CommonPrefixStatement (A : Assumptions) (k : Nat) : Prop :=
  ∀ exec : Execution, A.adversaryBounds → A.synchrony → CommonPrefix k exec

/-- Core chain-growth statement type. -/
def ChainGrowthStatement (A : Assumptions) : Prop :=
  ∀ exec : Execution, A.adversaryBounds → A.synchrony → ChainGrowth exec

/-- Core chain-quality statement type. -/
def ChainQualityStatement (A : Assumptions) : Prop :=
  ∀ exec : Execution, A.adversaryBounds → A.synchrony → ChainQuality exec

/-- Core transaction-inclusion statement type. -/
def TxInclusionStatement (A : Assumptions) : Prop :=
  ∀ exec : Execution, A.adversaryBounds → A.synchrony → TxInclusion exec

/-- Core leader-election fairness statement type. -/
def LeaderElectionFairnessStatement (A : Assumptions) : Prop :=
  ∀ exec : Execution, A.leaderElection → LeaderElectionFairness exec

/-- Protocol-specific assumption bundle, intended to be specialised to
    PoS-NSB, Ouroboros, PBFT, Tendermint, etc. -/
structure ProtocolInstance where
  name        : String
  assumptions : Assumptions

/-- For reference, a blueprint mapping from consensus `PropertyId`s to
    their intended core predicates, given an execution. At this stage,
    most properties are left as `True` and will be refined as dedicated
    developments are added. -/
def propertyHolds
    (exec : Execution)
    (p : Spec.PropertyId) : Prop :=
  match p with
  | .noForkTheorem        => NoFork exec
  | .commonPrefixProperty => ∃ k, CommonPrefix k exec
  | .chainGrowth          => ChainGrowth exec
  | .chainQuality         => ChainQuality exec
  | .transactionInclusion => TxInclusion exec
  | .leaderElectionFairness => LeaderElectionFairness exec
  | .noDoubleSpending     => NoDoubleSpending exec
  | .finalityGuarantee    => Finality exec
  | .slashingCorrectness  => SlashingCorrectness exec
  | .pbftSafety           => True
  | .tendermintConsensus  => True
  | .casperFFG            => True
  | .ouroboros            => True
  | .hotStuff             => True
  | .democraticBFT        => True
  | .nakamotoPoW          => True
  | .lmdGhost             => True
  | .lightClientCorrectness => LightClient.Statement
  | .merkleProofVerification => MerkleProof.Statement
  | .messagePassingSafety => MessagePassing.MessagePassingSafetyStatement
  | .replayAttackPrevention => MessagePassing.ReplayPreventionStatement
  | .lockedValueConservation => LockedValue.Statement
  | .validatorSetTransitions => ValidatorTransitions.Statement
  | .dataAvailability     => RollupDataAvailability.Statement
  | .sequencerCorrectness => RollupSequencer.Statement
  | .escapeHatch          => RollupEscapeHatch.Statement
  | .stateRootValidity    => RollupStateRoot.Statement
  | .gossipProtocolSafety => GossipProtocolSafety exec
  | .eclipseAttackResistance => EclipseAttackResistance exec
  | .dosResistance        => DosResistance exec
  | .merklePatriciaTrie   => MerklePatriciaTrie.Statement
  | .statePruningSafety   => StatePruning.Statement
  | .databaseConsistency  => DatabaseConsistency.Statement

end Core
end Consensus
end Blockchain
end HeytingLean
