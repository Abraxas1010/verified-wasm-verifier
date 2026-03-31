import HeytingLean.CCI.Core

/-
# Governance.Spec

Identifiers and metadata for governance, voting, and economic/game‑theoretic
properties from sections 6 and 7 of `crypto_proofs_master_list.md`.
-/

namespace HeytingLean
namespace Governance
namespace Spec

open HeytingLean.CCI

inductive PropertyId
  -- 6.1 Mechanism design
  | incentiveCompatibility
  | stakingEquilibrium
  | mevResistance
  | auctionTruthfulness
  -- 6.2 Economic security
  | costOfAttack
  | slashingDeterrence
  | inflationDeflationModels
  | liquidityMiningSafety
  -- 7.1 Voting mechanisms
  | ballotPrivacy
  | tallyCorrectness
  | coercionResistance
  | receiptFreeness
  -- 7.2 DAO governance
  | proposalExecutionCorrectness
  | timelockSecurity
  | quorumRequirements
  | vetoMechanismsCorrectness
  deriving DecidableEq, Repr

def PropertyId.slug : PropertyId → String
  | .incentiveCompatibility      => "econ.incentive_compatibility"
  | .stakingEquilibrium          => "econ.staking_equilibrium"
  | .mevResistance               => "econ.mev_resistance"
  | .auctionTruthfulness         => "econ.auction_truthfulness"
  | .costOfAttack                => "econ.cost_of_attack"
  | .slashingDeterrence          => "econ.slashing_deterrence"
  | .inflationDeflationModels    => "econ.inflation_deflation_models"
  | .liquidityMiningSafety       => "econ.liquidity_mining_safety"
  | .ballotPrivacy               => "gov.ballot_privacy"
  | .tallyCorrectness            => "gov.tally_correctness"
  | .coercionResistance          => "gov.coercion_resistance"
  | .receiptFreeness             => "gov.receipt_freeness"
  | .proposalExecutionCorrectness => "gov.proposal_execution_correctness"
  | .timelockSecurity            => "gov.timelock_security"
  | .quorumRequirements          => "gov.quorum_requirements"
  | .vetoMechanismsCorrectness   => "gov.veto_mechanisms_correctness"

def PropertyId.title : PropertyId → String
  | .incentiveCompatibility      => "Incentive Compatibility"
  | .stakingEquilibrium          => "Staking Equilibrium"
  | .mevResistance               => "MEV Resistance"
  | .auctionTruthfulness         => "Auction Truthfulness"
  | .costOfAttack                => "Cost of Attack"
  | .slashingDeterrence          => "Slashing Deterrence"
  | .inflationDeflationModels    => "Inflation/Deflation Models"
  | .liquidityMiningSafety       => "Liquidity Mining Safety"
  | .ballotPrivacy               => "Ballot Privacy"
  | .tallyCorrectness            => "Tally Correctness"
  | .coercionResistance          => "Coercion Resistance"
  | .receiptFreeness             => "Receipt-Freeness"
  | .proposalExecutionCorrectness => "Proposal Execution"
  | .timelockSecurity            => "Timelock Security"
  | .quorumRequirements          => "Quorum Requirements"
  | .vetoMechanismsCorrectness   => "Veto Mechanisms"

def PropertyId.description : PropertyId → String
  | .incentiveCompatibility =>
      "Honest behaviour is a (weakly) dominant or equilibrium strategy."
  | .stakingEquilibrium =>
      "Staking mechanisms support desired Nash equilibria under modelled incentives."
  | .mevResistance =>
      "Mechanisms limit extractable value from reordering or censoring."
  | .auctionTruthfulness =>
      "Auction design encourages truthful bidding strategies."
  | .costOfAttack =>
      "Economic analysis quantifies the cost of 51% or similar attacks."
  | .slashingDeterrence =>
      "Slashing penalties are sufficient to deter rational deviations."
  | .inflationDeflationModels =>
      "Token supply models behave as intended (inflation/deflation bounds)."
  | .liquidityMiningSafety =>
      "Liquidity mining rewards do not incentivise destabilising behaviour."
  | .ballotPrivacy =>
      "Votes remain secret from adversaries observing the protocol."
  | .tallyCorrectness =>
      "Vote tallies accurately reflect submitted ballots."
  | .coercionResistance =>
      "Voters cannot convincingly prove how they voted to a coercer."
  | .receiptFreeness =>
      "Voters obtain no transferable receipt of how they voted."
  | .proposalExecutionCorrectness =>
      "Passed DAO proposals execute exactly according to the decision logic."
  | .timelockSecurity =>
      "Timelock mechanisms enforce the required delay before execution."
  | .quorumRequirements =>
      "Quorum rules ensure sufficient participation for decisions."
  | .vetoMechanismsCorrectness =>
      "Veto and emergency-stop mechanisms function as specified."

def PropertyId.toExpr (p : PropertyId) : Expr :=
  Expr.atom p.slug

end Spec
end Governance
end HeytingLean
