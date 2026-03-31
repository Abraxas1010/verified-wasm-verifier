import HeytingLean.Basic
import HeytingLean.CCI.Core

/-
# Blockchain.Consensus.Spec

Identifier and metadata layer for consensus‑level properties from
`WIP/crypto_proofs_master_list.md` (section 1 and related bridge/infra rows).

This module does **not** fix a particular semantic model yet; it provides
canonical names that other modules (and CCI certificates) can reuse.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace Spec

open HeytingLean.CCI

/-- Consensus‑level properties (safety, liveness, and protocol‑specific). -/
inductive PropertyId
  | noForkTheorem
  | commonPrefixProperty
  | noDoubleSpending
  | finalityGuarantee
  | slashingCorrectness
  | chainGrowth
  | chainQuality
  | transactionInclusion
  | leaderElectionFairness
  | pbftSafety
  | tendermintConsensus
  | casperFFG
  | ouroboros
  | hotStuff
  | democraticBFT
  | nakamotoPoW
  | lmdGhost
  | lightClientCorrectness
  | merkleProofVerification
  | messagePassingSafety
  | replayAttackPrevention
  | lockedValueConservation
  | validatorSetTransitions
  | dataAvailability
  | sequencerCorrectness
  | escapeHatch
  | stateRootValidity
  | gossipProtocolSafety
  | eclipseAttackResistance
  | dosResistance
  | merklePatriciaTrie
  | statePruningSafety
  | databaseConsistency
  deriving DecidableEq, Repr

/-- Canonical, machine‑friendly slug for a consensus property. -/
def PropertyId.slug : PropertyId → String
  | .noForkTheorem        => "consensus.no_fork"
  | .commonPrefixProperty => "consensus.common_prefix"
  | .noDoubleSpending     => "consensus.no_double_spend"
  | .finalityGuarantee    => "consensus.finality_guarantee"
  | .slashingCorrectness  => "consensus.slashing_correctness"
  | .chainGrowth          => "consensus.chain_growth"
  | .chainQuality         => "consensus.chain_quality"
  | .transactionInclusion => "consensus.transaction_inclusion"
  | .leaderElectionFairness => "consensus.leader_election_fairness"
  | .pbftSafety           => "consensus.pbft_safety"
  | .tendermintConsensus  => "consensus.tendermint"
  | .casperFFG            => "consensus.casper_ffg"
  | .ouroboros            => "consensus.ouroboros"
  | .hotStuff             => "consensus.hotstuff"
  | .democraticBFT        => "consensus.democratic_bft"
  | .nakamotoPoW          => "consensus.nakamoto_pow"
  | .lmdGhost             => "consensus.lmd_ghost"
  | .lightClientCorrectness => "bridge.light_client_correctness"
  | .merkleProofVerification => "bridge.merkle_proof_verification"
  | .messagePassingSafety => "bridge.message_passing_safety"
  | .replayAttackPrevention => "bridge.replay_attack_prevention"
  | .lockedValueConservation => "bridge.locked_value_conservation"
  | .validatorSetTransitions => "bridge.validator_set_transitions"
  | .dataAvailability     => "rollup.data_availability"
  | .sequencerCorrectness => "rollup.sequencer_correctness"
  | .escapeHatch          => "rollup.escape_hatch"
  | .stateRootValidity    => "rollup.state_root_validity"
  | .gossipProtocolSafety => "infra.gossip_protocol_safety"
  | .eclipseAttackResistance => "infra.eclipse_attack_resistance"
  | .dosResistance        => "infra.dos_resistance"
  | .merklePatriciaTrie   => "infra.merkle_patricia_trie"
  | .statePruningSafety   => "infra.state_pruning_safety"
  | .databaseConsistency  => "infra.database_consistency"

/-- Human‑readable title mirroring the master list. -/
def PropertyId.title : PropertyId → String
  | .noForkTheorem          => "No-Fork Theorem"
  | .commonPrefixProperty   => "Common Prefix Property"
  | .noDoubleSpending       => "No Double-Spending"
  | .finalityGuarantee      => "Finality Guarantee"
  | .slashingCorrectness    => "Slashing Correctness"
  | .chainGrowth            => "Chain Growth"
  | .chainQuality           => "Chain Quality"
  | .transactionInclusion   => "Transaction Inclusion"
  | .leaderElectionFairness => "Leader Election Fairness"
  | .pbftSafety             => "PBFT Safety"
  | .tendermintConsensus    => "Tendermint Consensus"
  | .casperFFG              => "Casper FFG"
  | .ouroboros              => "Ouroboros (Cardano)"
  | .hotStuff               => "HotStuff"
  | .democraticBFT          => "Democratic BFT"
  | .nakamotoPoW            => "Nakamoto PoW"
  | .lmdGhost               => "LMD-GHOST"
  | .lightClientCorrectness => "Light Client Correctness"
  | .merkleProofVerification => "Merkle Proof Verification"
  | .messagePassingSafety   => "Message Passing Safety"
  | .replayAttackPrevention => "Replay Attack Prevention"
  | .lockedValueConservation => "Locked Value Conservation"
  | .validatorSetTransitions => "Validator Set Transitions"
  | .dataAvailability       => "Data Availability"
  | .sequencerCorrectness   => "Sequencer Correctness"
  | .escapeHatch            => "Escape Hatch"
  | .stateRootValidity      => "State Root Validity"
  | .gossipProtocolSafety   => "Gossip Protocol Safety"
  | .eclipseAttackResistance => "Eclipse Attack Resistance"
  | .dosResistance          => "DoS Resistance"
  | .merklePatriciaTrie     => "Merkle Patricia Trie"
  | .statePruningSafety     => "State Pruning Safety"
  | .databaseConsistency    => "Database Consistency"

/-- Basic description string, compatible with the master list table. -/
def PropertyId.description : PropertyId → String
  | .noForkTheorem =>
      "Two different blocks cannot be certified in the same round."
  | .commonPrefixProperty =>
      "Honest nodes agree on a shared history up to k blocks."
  | .noDoubleSpending =>
      "A transaction output cannot be spent twice."
  | .finalityGuarantee =>
      "Once finalized, transactions cannot be reverted."
  | .slashingCorrectness =>
      "Validators are only slashed for provable violations."
  | .chainGrowth =>
      "The blockchain grows at at least the minimum expected rate."
  | .chainQuality =>
      "A minimum fraction of blocks comes from honest participants."
  | .transactionInclusion =>
      "Valid transactions are eventually included in the chain."
  | .leaderElectionFairness =>
      "Leader election is proportional to stake (or configured weight)."
  | .pbftSafety =>
      "PBFT achieves safety with at most f Byzantine faults among 3f+1 nodes."
  | .tendermintConsensus =>
      "Tendermint maintains safety under partial synchrony assumptions."
  | .casperFFG =>
      "Casper FFG finality gadget preserves safety and liveness assumptions."
  | .ouroboros =>
      "Ouroboros PoS protocols satisfy the standard security properties."
  | .hotStuff =>
      "HotStuff’s linear view-change protocol preserves BFT safety."
  | .democraticBFT =>
      "Democratic BFT-style protocols satisfy their stated safety guarantees."
  | .nakamotoPoW =>
      "Nakamoto longest-chain consensus achieves probabilistic safety."
  | .lmdGhost =>
      "LMD-GHOST fork-choice rule selects a safe chain under given assumptions."
  | .lightClientCorrectness =>
      "Light clients validate headers and associated proofs correctly."
  | .merkleProofVerification =>
      "Cross-chain Merkle proofs correctly witness membership and state."
  | .messagePassingSafety =>
      "No duplicate or lost messages across chains under the bridge protocol."
  | .replayAttackPrevention =>
      "Bridge messages cannot be replayed across time or chains."
  | .lockedValueConservation =>
      "Total value minted on the destination chain equals total value locked on the source chain."
  | .validatorSetTransitions =>
      "Validator-set handoffs between epochs preserve a secure overlap between successive validator sets."
  | .dataAvailability =>
      "Rollup data is available so transitions can be reconstructed."
  | .sequencerCorrectness =>
      "The sequencer orders transactions according to the protocol rules."
  | .escapeHatch =>
      "Users can safely exit a rollup without relying on the sequencer."
  | .stateRootValidity =>
      "Posted state roots match the execution of the underlying state machine."
  | .gossipProtocolSafety =>
      "Gossip protocols propagate messages without violating safety."
  | .eclipseAttackResistance =>
      "Network resists eclipse attacks within stated parameters."
  | .dosResistance =>
      "Rate limiting and resource bounds prevent DoS escalation."
  | .merklePatriciaTrie =>
      "Merkle Patricia Trie correctly represents the underlying key-value state."
  | .statePruningSafety =>
      "State pruning preserves required historical data availability."
  | .databaseConsistency =>
      "Chain database satisfies ACID-like consistency properties."

/-- Canonical CCI expression for a consensus property: a single atom. -/
def PropertyId.toExpr (p : PropertyId) : Expr :=
  Expr.atom p.slug

end Spec
end Consensus
end Blockchain
end HeytingLean
