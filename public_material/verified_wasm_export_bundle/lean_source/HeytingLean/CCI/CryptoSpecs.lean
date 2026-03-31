import HeytingLean.CCI.Core
import HeytingLean.CCI.Cert
import HeytingLean.CCI.Check
import HeytingLean.Blockchain.Consensus.Spec
import HeytingLean.Blockchain.Contracts.Spec
import HeytingLean.Crypto.Primitives.Spec
import HeytingLean.Crypto.ZK.Spec
import HeytingLean.Governance.Spec
import HeytingLean.Privacy.Spec

/-
# CCI.CryptoSpecs

Canonical identifiers for all entries in `crypto_proofs_master_list.md`
and helpers to map them into the core CCI `Expr`/`Certificate` layer.

This module does **not** encode semantic content; it provides a clean,
central registry of property IDs and a standard way to generate minimal
certificates whose omega-expression is a single atom tagged by a slug.
-/

namespace HeytingLean
namespace CCI
namespace CryptoSpecs

open HeytingLean.Blockchain
open HeytingLean.Crypto
open HeytingLean.Governance
open HeytingLean.Privacy

/-! ## Global property identifier -/

/-- Global crypto property identifier, spanning all domains. -/
inductive Property
  | consensus (p : Blockchain.Consensus.Spec.PropertyId)
  | contracts (p : Blockchain.Contracts.Spec.PropertyId)
  | primitives (p : Crypto.Primitives.Spec.PropertyId)
  | zk        (p : Crypto.ZK.Spec.PropertyId)
  | governance (p : Governance.Spec.PropertyId)
  | privacy   (p : Privacy.Spec.PropertyId)
  deriving Repr

namespace Property

/-- Canonical slug, delegated to the domain-specific spec modules. -/
def slug : Property → String
  | .consensus p  => p.slug
  | .contracts p  => p.slug
  | .primitives p => p.slug
  | .zk p         => p.slug
  | .governance p => p.slug
  | .privacy p    => p.slug

/-- Human-readable title. -/
def title : Property → String
  | .consensus p  => p.title
  | .contracts p  => p.title
  | .primitives p => p.title
  | .zk p         => p.title
  | .governance p => p.title
  | .privacy p    => p.title

/-- Short description compatible with the master list. -/
def description : Property → String
  | .consensus p  => p.description
  | .contracts p  => p.description
  | .primitives p => p.description
  | .zk p         => p.description
  | .governance p => p.description
  | .privacy p    => p.description

/-- Enumeration of all crypto properties across domains.

This list is the single source of truth for mapping canonical slugs
(`Property.slug`) to global `Property` identifiers. Every row in
`crypto_proofs_master_list.md` should appear exactly once here via its
domain-specific `PropertyId`. -/
def all : List Property :=
  [
    -- Consensus and bridge/infra/rollup rows
    .consensus Blockchain.Consensus.Spec.PropertyId.noForkTheorem,
    .consensus Blockchain.Consensus.Spec.PropertyId.commonPrefixProperty,
    .consensus Blockchain.Consensus.Spec.PropertyId.noDoubleSpending,
    .consensus Blockchain.Consensus.Spec.PropertyId.finalityGuarantee,
    .consensus Blockchain.Consensus.Spec.PropertyId.slashingCorrectness,
    .consensus Blockchain.Consensus.Spec.PropertyId.chainGrowth,
    .consensus Blockchain.Consensus.Spec.PropertyId.chainQuality,
    .consensus Blockchain.Consensus.Spec.PropertyId.transactionInclusion,
    .consensus Blockchain.Consensus.Spec.PropertyId.leaderElectionFairness,
    .consensus Blockchain.Consensus.Spec.PropertyId.pbftSafety,
    .consensus Blockchain.Consensus.Spec.PropertyId.tendermintConsensus,
    .consensus Blockchain.Consensus.Spec.PropertyId.casperFFG,
    .consensus Blockchain.Consensus.Spec.PropertyId.ouroboros,
    .consensus Blockchain.Consensus.Spec.PropertyId.hotStuff,
    .consensus Blockchain.Consensus.Spec.PropertyId.democraticBFT,
    .consensus Blockchain.Consensus.Spec.PropertyId.nakamotoPoW,
    .consensus Blockchain.Consensus.Spec.PropertyId.lmdGhost,
    .consensus Blockchain.Consensus.Spec.PropertyId.lightClientCorrectness,
    .consensus Blockchain.Consensus.Spec.PropertyId.merkleProofVerification,
    .consensus Blockchain.Consensus.Spec.PropertyId.messagePassingSafety,
    .consensus Blockchain.Consensus.Spec.PropertyId.replayAttackPrevention,
    .consensus Blockchain.Consensus.Spec.PropertyId.lockedValueConservation,
    .consensus Blockchain.Consensus.Spec.PropertyId.validatorSetTransitions,
    .consensus Blockchain.Consensus.Spec.PropertyId.dataAvailability,
    .consensus Blockchain.Consensus.Spec.PropertyId.sequencerCorrectness,
    .consensus Blockchain.Consensus.Spec.PropertyId.escapeHatch,
    .consensus Blockchain.Consensus.Spec.PropertyId.stateRootValidity,
    .consensus Blockchain.Consensus.Spec.PropertyId.gossipProtocolSafety,
    .consensus Blockchain.Consensus.Spec.PropertyId.eclipseAttackResistance,
    .consensus Blockchain.Consensus.Spec.PropertyId.dosResistance,
    .consensus Blockchain.Consensus.Spec.PropertyId.merklePatriciaTrie,
    .consensus Blockchain.Consensus.Spec.PropertyId.statePruningSafety,
    .consensus Blockchain.Consensus.Spec.PropertyId.databaseConsistency,

    -- Contracts / DeFi / semantics rows
    .contracts Blockchain.Contracts.Spec.PropertyId.reentrancyAbsence,
    .contracts Blockchain.Contracts.Spec.PropertyId.integerOverflowUnderflow,
    .contracts Blockchain.Contracts.Spec.PropertyId.accessControlCorrectness,
    .contracts Blockchain.Contracts.Spec.PropertyId.frontRunningResistance,
    .contracts Blockchain.Contracts.Spec.PropertyId.flashLoanResistance,
    .contracts Blockchain.Contracts.Spec.PropertyId.oracleManipulationResistance,
    .contracts Blockchain.Contracts.Spec.PropertyId.erc20Correctness,
    .contracts Blockchain.Contracts.Spec.PropertyId.erc721Correctness,
    .contracts Blockchain.Contracts.Spec.PropertyId.erc1155Correctness,
    .contracts Blockchain.Contracts.Spec.PropertyId.erc4626Correctness,
    .contracts Blockchain.Contracts.Spec.PropertyId.governorContractsCorrectness,
    .contracts Blockchain.Contracts.Spec.PropertyId.ammConstantProduct,
    .contracts Blockchain.Contracts.Spec.PropertyId.ammArbitrageOptimality,
    .contracts Blockchain.Contracts.Spec.PropertyId.lendingPoolSolvency,
    .contracts Blockchain.Contracts.Spec.PropertyId.liquidationCorrectness,
    .contracts Blockchain.Contracts.Spec.PropertyId.interestRateModelCorrectness,
    .contracts Blockchain.Contracts.Spec.PropertyId.stakingRewardsDistribution,
    .contracts Blockchain.Contracts.Spec.PropertyId.perpetualFundingRate,
    .contracts Blockchain.Contracts.Spec.PropertyId.evmSemantics,
    .contracts Blockchain.Contracts.Spec.PropertyId.soliditySemantics,
    .contracts Blockchain.Contracts.Spec.PropertyId.vyperSemantics,
    .contracts Blockchain.Contracts.Spec.PropertyId.moveSemantics,
    .contracts Blockchain.Contracts.Spec.PropertyId.cairoSemantics,

    -- Cryptographic primitives and post-quantum rows
    .primitives Crypto.Primitives.Spec.PropertyId.keccak256Correctness,
    .primitives Crypto.Primitives.Spec.PropertyId.poseidonHashCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.blake3Correctness,
    .primitives Crypto.Primitives.Spec.PropertyId.pedersenHashCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.hashCollisionResistance,
    .primitives Crypto.Primitives.Spec.PropertyId.ecdsaCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.eddsaCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.blsSignaturesCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.schnorrSignaturesCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.thresholdSignaturesCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.multiSignaturesCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.aesGcmCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.chacha20Poly1305Correctness,
    .primitives Crypto.Primitives.Spec.PropertyId.eciesCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.homomorphicEncryptionCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.pedersenCommitmentsSecurity,
    .primitives Crypto.Primitives.Spec.PropertyId.kzgCommitmentsCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.merkleTreeProofsCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.vectorCommitmentsCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.dilithiumCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.sphincsPlusCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.falconCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.latticeEncryptionCorrectness,
    .primitives Crypto.Primitives.Spec.PropertyId.hashBasedCommitmentsPQ,
    .primitives Crypto.Primitives.Spec.PropertyId.starkQuantumSafety,

    -- ZK systems and ZK applications
    .zk Crypto.ZK.Spec.PropertyId.groth16Soundness,
    .zk Crypto.ZK.Spec.PropertyId.plonkSoundness,
    .zk Crypto.ZK.Spec.PropertyId.halo2Correctness,
    .zk Crypto.ZK.Spec.PropertyId.r1csSatisfiability,
    .zk Crypto.ZK.Spec.PropertyId.circuitCompilationCorrectness,
    .zk Crypto.ZK.Spec.PropertyId.friProtocolCorrectness,
    .zk Crypto.ZK.Spec.PropertyId.airConstraintsCorrectness,
    .zk Crypto.ZK.Spec.PropertyId.starkSoundness,
    .zk Crypto.ZK.Spec.PropertyId.cairoExecutionCorrectness,
    .zk Crypto.ZK.Spec.PropertyId.zkRollupStateTransition,
    .zk Crypto.ZK.Spec.PropertyId.zkEvmEquivalence,
    .zk Crypto.ZK.Spec.PropertyId.privateVotingCorrectness,
    .zk Crypto.ZK.Spec.PropertyId.anonymousCredentialsCorrectness,
    .zk Crypto.ZK.Spec.PropertyId.rangeProofsCorrectness,
    .zk Crypto.ZK.Spec.PropertyId.fraudProofValidity,
    .zk Crypto.ZK.Spec.PropertyId.zkBridgeSoundness,

    -- Governance, voting, and economics
    .governance Governance.Spec.PropertyId.incentiveCompatibility,
    .governance Governance.Spec.PropertyId.stakingEquilibrium,
    .governance Governance.Spec.PropertyId.mevResistance,
    .governance Governance.Spec.PropertyId.auctionTruthfulness,
    .governance Governance.Spec.PropertyId.costOfAttack,
    .governance Governance.Spec.PropertyId.slashingDeterrence,
    .governance Governance.Spec.PropertyId.inflationDeflationModels,
    .governance Governance.Spec.PropertyId.liquidityMiningSafety,
    .governance Governance.Spec.PropertyId.ballotPrivacy,
    .governance Governance.Spec.PropertyId.tallyCorrectness,
    .governance Governance.Spec.PropertyId.coercionResistance,
    .governance Governance.Spec.PropertyId.receiptFreeness,
    .governance Governance.Spec.PropertyId.proposalExecutionCorrectness,
    .governance Governance.Spec.PropertyId.timelockSecurity,
    .governance Governance.Spec.PropertyId.quorumRequirements,
    .governance Governance.Spec.PropertyId.vetoMechanismsCorrectness,

    -- Privacy and mixer/CT properties
    .privacy Privacy.Spec.PropertyId.tornadoCashLogic,
    .privacy Privacy.Spec.PropertyId.mixerAnonymitySet,
    .privacy Privacy.Spec.PropertyId.nullifierUniqueness,
    .privacy Privacy.Spec.PropertyId.amountHiding,
    .privacy Privacy.Spec.PropertyId.balanceProofs,
    .privacy Privacy.Spec.PropertyId.assetTypeHiding
  ]

/-- Canonical CCI expression: a single atom keyed by the property slug. -/
def toExpr (p : Property) : Expr :=
  Expr.atom p.slug

end Property

/-! ## Minimal certificates for properties -/

/-- Build a minimal certificate for a property with the given public inputs.

The certificate has:
- `omega` equal to the atom identified by the property slug;
- empty lens image and rewrites;
- a single `"omega"` digest field matching `hashExpr (canon omega)`.

This is the structurally simplest certificate that the core checker will
accept for a given property identifier.
-/
def mkPropertyCertificate (p : Property)
    (inputs : PublicInputs := []) : Certificate :=
  let omega := Property.toExpr p
  let omegaCanon := HeytingLean.CCI.canon omega
  let d := hashExpr omegaCanon
  let digests : List (Path × Digest) := [("omega", d)]
  { inputs := inputs
  , omega := omega
  , lensImgs := []
  , rewrites := []
  , digests := digests }

/-- Variant of `mkPropertyCertificate` that works directly from a slug.

This is convenient for CLIs that only know the textual identifier and do
not need the richer `Property` metadata yet. -/
def mkCertificateFromSlug (slug : String)
    (inputs : PublicInputs := []) : Certificate :=
  let omega := Expr.atom slug
  let omegaCanon := HeytingLean.CCI.canon omega
  let d := hashExpr omegaCanon
  let digests : List (Path × Digest) := [("omega", d)]
  { inputs := inputs
  , omega := omega
  , lensImgs := []
  , rewrites := []
  , digests := digests }

/-- Resolve a property slug string to the global `Property` identifier.

This is driven entirely by `Property.all`, so every slug exposed by the
domain-specific `PropertyId.slug` helpers is recognised here. -/
def propertyOfSlug? (slug : String) : Option Property :=
  Property.all.find? (fun p => Property.slug p = slug)

end CryptoSpecs
end CCI
end HeytingLean
