import HeytingLean.CCI.CryptoSpecs
import HeytingLean.Blockchain.Consensus.Spec
import HeytingLean.Blockchain.Contracts.Spec
import HeytingLean.Blockchain.Contracts.Model
import HeytingLean.DeFi.Model
import HeytingLean.DeFi.AMM
import HeytingLean.Crypto.Primitives.Spec
import HeytingLean.Crypto.ZK.Spec
import HeytingLean.Crypto.ZK.Spec.R1CS
import HeytingLean.Crypto.ZK.Spec.AIR
import HeytingLean.Governance.Spec
import HeytingLean.Governance.Model
import HeytingLean.Privacy.Spec

/-
# Crypto.Registry

Lightweight registry helpers tying together:
* the global crypto property identifier (`CCI.CryptoSpecs.Property`);
* master-list style keys (section/category + slug); and
* optional links to main Lean theorem names.

This module is intentionally minimal: it provides a stable interface that
tooling and CLIs can use to navigate between the textual master list,
domain-specific `PropertyId`s, and Lean declarations.
-/

namespace HeytingLean
namespace Crypto
namespace Registry

open HeytingLean.CCI
open HeytingLean.Blockchain
open HeytingLean.Governance
open HeytingLean.Privacy

/-- Alias for the global crypto property identifier. -/
abbrev Property := CCI.CryptoSpecs.Property

/-- Canonical master-list style key for a property.

The key is a simple `"<domain>:<slug>"` string, where `<slug>` is the
domain-specific identifier (e.g. `"consensus.no_fork"`,
`"defi.amm_constant_product"`). This keeps the mapping lightweight while
remaining stable enough for tools and docs. -/
def masterListKey : Property → String
  | .consensus p  => "consensus:"  ++ p.slug
  | .contracts p  => "contracts:"  ++ p.slug
  | .primitives p => "primitives:" ++ p.slug
  | .zk p         => "zk:"         ++ p.slug
  | .governance p => "governance:" ++ p.slug
  | .privacy p    => "privacy:"    ++ p.slug

/-- Optional mapping from a property to the main Lean theorem name that
    realises it.

At this stage most properties do not yet have concrete theorems, so this
function returns `none` in most cases. As proofs are added, entries can be
filled in to point tools and docs back to the corresponding declarations. -/
def theoremName? : Property → Option Lean.Name
  | .consensus p =>
      match p with
      | Blockchain.Consensus.Spec.PropertyId.noForkTheorem =>
          some `HeytingLean.Blockchain.Consensus.Core.noForkTheorem_equalChains
      | Blockchain.Consensus.Spec.PropertyId.commonPrefixProperty =>
          some `HeytingLean.Blockchain.Consensus.Core.commonPrefixTheorem_equalChains
      | Blockchain.Consensus.Spec.PropertyId.finalityGuarantee =>
          some `HeytingLean.Blockchain.Consensus.LivenessExample.propertyHolds_finality_growingExecution
      | Blockchain.Consensus.Spec.PropertyId.noDoubleSpending =>
          some `HeytingLean.Blockchain.Consensus.LivenessExample.propertyHolds_noDoubleSpending_growingExecution
      | Blockchain.Consensus.Spec.PropertyId.slashingCorrectness =>
          some `HeytingLean.Blockchain.Consensus.LivenessExample.propertyHolds_slashingCorrectness_growingExecution
      | Blockchain.Consensus.Spec.PropertyId.lightClientCorrectness =>
          some `HeytingLean.Blockchain.Consensus.LightClient.statement_holds
      | Blockchain.Consensus.Spec.PropertyId.merkleProofVerification =>
          some `HeytingLean.Blockchain.Consensus.MerkleProof.statement_holds
      | Blockchain.Consensus.Spec.PropertyId.messagePassingSafety =>
          some `HeytingLean.Blockchain.Consensus.MessagePassing.messagePassingSafetyStatement_holds
      | Blockchain.Consensus.Spec.PropertyId.replayAttackPrevention =>
          some `HeytingLean.Blockchain.Consensus.MessagePassing.replayPreventionStatement_holds
      | Blockchain.Consensus.Spec.PropertyId.lockedValueConservation =>
          some `HeytingLean.Blockchain.Consensus.LockedValue.statement_holds
      | Blockchain.Consensus.Spec.PropertyId.validatorSetTransitions =>
          some `HeytingLean.Blockchain.Consensus.ValidatorTransitions.statement_holds
      | Blockchain.Consensus.Spec.PropertyId.dataAvailability =>
          some `HeytingLean.Blockchain.Consensus.RollupDataAvailability.statement_holds
      | Blockchain.Consensus.Spec.PropertyId.sequencerCorrectness =>
          some `HeytingLean.Blockchain.Consensus.RollupSequencer.statement_holds
      | Blockchain.Consensus.Spec.PropertyId.escapeHatch =>
          some `HeytingLean.Blockchain.Consensus.RollupEscapeHatch.statement_holds
      | Blockchain.Consensus.Spec.PropertyId.stateRootValidity =>
          some `HeytingLean.Blockchain.Consensus.RollupStateRoot.statement_holds
      | Blockchain.Consensus.Spec.PropertyId.gossipProtocolSafety =>
          some `HeytingLean.Blockchain.Consensus.InfraExample.propertyHolds_gossipProtocolSafety_infraExecution
      | Blockchain.Consensus.Spec.PropertyId.eclipseAttackResistance =>
          some `HeytingLean.Blockchain.Consensus.InfraExample.propertyHolds_eclipseAttackResistance_infraExecution
      | Blockchain.Consensus.Spec.PropertyId.dosResistance =>
          some `HeytingLean.Blockchain.Consensus.InfraExample.propertyHolds_dosResistance_infraExecution
      | Blockchain.Consensus.Spec.PropertyId.chainGrowth =>
          some `HeytingLean.Blockchain.Consensus.LivenessExample.propertyHolds_chainGrowth_growingExecution
      | Blockchain.Consensus.Spec.PropertyId.chainQuality =>
          some `HeytingLean.Blockchain.Consensus.LivenessExample.propertyHolds_chainQuality_growingExecution
      | Blockchain.Consensus.Spec.PropertyId.transactionInclusion =>
          some `HeytingLean.Blockchain.Consensus.LivenessExample.propertyHolds_transactionInclusion_growingExecution
      | Blockchain.Consensus.Spec.PropertyId.leaderElectionFairness =>
          some `HeytingLean.Blockchain.Consensus.LivenessExample.propertyHolds_leaderElectionFairness_growingExecution
      | _ => none
  | .contracts p =>
      match p with
      | Blockchain.Contracts.Spec.PropertyId.erc20Correctness =>
          some `HeytingLean.Blockchain.Contracts.Model.erc20InvariantStatement_holds
      | Blockchain.Contracts.Spec.PropertyId.ammConstantProduct =>
          some `HeytingLean.DeFi.AMM.constantProductStatement_holds
      | Blockchain.Contracts.Spec.PropertyId.ammArbitrageOptimality =>
          some `HeytingLean.DeFi.AMM.arbitrageOptimalityStatement_holds
      | Blockchain.Contracts.Spec.PropertyId.lendingPoolSolvency =>
          some `HeytingLean.DeFi.Lending.lendingSequenceSolvencyStatement_holds
      | Blockchain.Contracts.Spec.PropertyId.liquidationCorrectness =>
          some `HeytingLean.DeFi.Lending.liquidationCorrectnessStatement_holds
      | Blockchain.Contracts.Spec.PropertyId.interestRateModelCorrectness =>
          some `HeytingLean.DeFi.Lending.interestRateModelStatement_holds
      | Blockchain.Contracts.Spec.PropertyId.stakingRewardsDistribution =>
          some `HeytingLean.DeFi.Lending.stakingRewardsStatement_holds
      | _ => none
  | .privacy p =>
      match p with
      | Privacy.Spec.PropertyId.tornadoCashLogic =>
          some `HeytingLean.Privacy.Spec.propertyHolds_tornadoCashLogic
      | Privacy.Spec.PropertyId.mixerAnonymitySet =>
          some `HeytingLean.Privacy.Spec.propertyHolds_mixerAnonymitySet
      | Privacy.Spec.PropertyId.nullifierUniqueness =>
          some `HeytingLean.Privacy.Spec.propertyHolds_nullifierUniqueness
      | Privacy.Spec.PropertyId.amountHiding =>
          some `HeytingLean.Privacy.Spec.propertyHolds_amountHiding
      | Privacy.Spec.PropertyId.balanceProofs =>
          some `HeytingLean.Privacy.Spec.propertyHolds_balanceProofs
      | Privacy.Spec.PropertyId.assetTypeHiding =>
          some `HeytingLean.Privacy.Spec.propertyHolds_assetTypeHiding
  | .primitives p =>
      match p with
      | Crypto.Primitives.Spec.PropertyId.merkleTreeProofsCorrectness =>
          some `HeytingLean.Crypto.Primitives.Spec.merkleTreeProofsCorrectnessStatement_holds
      | Crypto.Primitives.Spec.PropertyId.poseidonHashCorrectness =>
          some `HeytingLean.Crypto.Primitives.Spec.poseidonHashCorrectnessStatement_holds
      | Crypto.Primitives.Spec.PropertyId.kzgCommitmentsCorrectness =>
          some `HeytingLean.Crypto.Primitives.Spec.demoPolyCommitmentCorrectnessStatement_holds
      | Crypto.Primitives.Spec.PropertyId.vectorCommitmentsCorrectness =>
          some `HeytingLean.Crypto.Primitives.Spec.demoVectorCommitmentCorrectnessStatement_holds
      | _ => none
  | .zk p =>
      match p with
      | Crypto.ZK.Spec.PropertyId.halo2Correctness =>
          some `HeytingLean.Crypto.ZK.Spec.Halo2.correctnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.friProtocolCorrectness =>
          some `HeytingLean.Crypto.ZK.Spec.FRI.soundnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.cairoExecutionCorrectness =>
          some `HeytingLean.Crypto.ZK.Spec.Cairo.executionCorrectnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.zkEvmEquivalence =>
          some `HeytingLean.Crypto.ZK.Spec.ZkEvm.equivalenceStatement_holds
      | Crypto.ZK.Spec.PropertyId.plonkSoundness =>
          some `HeytingLean.Crypto.ZK.Spec.Plonk.soundnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.groth16Soundness =>
          some `HeytingLean.Crypto.ZK.Spec.Groth16.soundnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.airConstraintsCorrectness =>
          some `HeytingLean.Crypto.ZK.Spec.AIR.constraintsCorrectnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.starkSoundness =>
          some `HeytingLean.Crypto.ZK.Spec.STARK.starkSoundnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.zkRollupStateTransition =>
          some `HeytingLean.Crypto.ZK.Spec.zkRollupStateTransitionStatement_holds
      | Crypto.ZK.Spec.PropertyId.r1csSatisfiability =>
          some `HeytingLean.Crypto.ZK.Spec.R1CS.satisfiabilityStatement_holds
      | Crypto.ZK.Spec.PropertyId.circuitCompilationCorrectness =>
          some `HeytingLean.Crypto.ZK.Spec.R1CS.compilationCorrectnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.fraudProofValidity =>
          some `HeytingLean.Crypto.ZK.Spec.fraudProofValidityStatement_holds
      | Crypto.ZK.Spec.PropertyId.zkBridgeSoundness =>
          some `HeytingLean.Crypto.ZK.Spec.zkBridgeSoundnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.rangeProofsCorrectness =>
          some `HeytingLean.Crypto.ZK.Spec.rangeProofsCorrectnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.privateVotingCorrectness =>
          some `HeytingLean.Crypto.ZK.Spec.privateVotingCorrectnessStatement_holds
      | Crypto.ZK.Spec.PropertyId.anonymousCredentialsCorrectness =>
          some `HeytingLean.Crypto.ZK.Spec.anonymousCredentialsCorrectnessStatement_holds
  | .governance p =>
      match p with
      | Governance.Spec.PropertyId.tallyCorrectness =>
          some `HeytingLean.Governance.Model.tallyBallots_correct
      | Governance.Spec.PropertyId.proposalExecutionCorrectness =>
          some `HeytingLean.Governance.Model.exampleDAOState_ProposalExecutionCorrect
      | Governance.Spec.PropertyId.timelockSecurity =>
          some `HeytingLean.Governance.Model.exampleDAOState_TimelockSecurity
      | Governance.Spec.PropertyId.vetoMechanismsCorrectness =>
          some `HeytingLean.Governance.Model.exampleDAOState_VetoMechanismsCorrect
      | Governance.Spec.PropertyId.incentiveCompatibility =>
          some `HeytingLean.Economics.Game.Bridge.propertyHolds_incentiveCompatibility_trivialGame
      | Governance.Spec.PropertyId.stakingEquilibrium =>
          some `HeytingLean.Economics.Game.Bridge.propertyHolds_stakingEquilibrium_stakingGame
      | Governance.Spec.PropertyId.auctionTruthfulness =>
          some `HeytingLean.Economics.Game.Bridge.propertyHolds_auctionTruthfulness_secondPrice
      | _ => none

end Registry
end Crypto
end HeytingLean
