import HeytingLean.CCI.Core

/-
# Blockchain.Contracts.Spec

Identifier and metadata layer for smart‑contract and DeFi properties from
`WIP/crypto_proofs_master_list.md` (section 2).
-/

namespace HeytingLean
namespace Blockchain
namespace Contracts
namespace Spec

open HeytingLean.CCI

inductive PropertyId
  | reentrancyAbsence
  | integerOverflowUnderflow
  | accessControlCorrectness
  | frontRunningResistance
  | flashLoanResistance
  | oracleManipulationResistance
  | erc20Correctness
  | erc721Correctness
  | erc1155Correctness
  | erc4626Correctness
  | governorContractsCorrectness
  | ammConstantProduct
  | ammArbitrageOptimality
  | lendingPoolSolvency
  | liquidationCorrectness
  | interestRateModelCorrectness
  | stakingRewardsDistribution
  | perpetualFundingRate
  | evmSemantics
  | soliditySemantics
  | vyperSemantics
  | moveSemantics
  | cairoSemantics
  deriving DecidableEq, Repr

def PropertyId.slug : PropertyId → String
  | .reentrancyAbsence        => "contracts.reentrancy_absence"
  | .integerOverflowUnderflow => "contracts.integer_overflow_underflow"
  | .accessControlCorrectness => "contracts.access_control_correctness"
  | .frontRunningResistance   => "contracts.front_running_resistance"
  | .flashLoanResistance      => "contracts.flash_loan_resistance"
  | .oracleManipulationResistance => "contracts.oracle_manipulation_resistance"
  | .erc20Correctness         => "contracts.erc20_correctness"
  | .erc721Correctness        => "contracts.erc721_correctness"
  | .erc1155Correctness       => "contracts.erc1155_correctness"
  | .erc4626Correctness       => "contracts.erc4626_correctness"
  | .governorContractsCorrectness => "contracts.governor_contracts_correctness"
  | .ammConstantProduct       => "defi.amm_constant_product"
  | .ammArbitrageOptimality   => "defi.amm_arbitrage_optimality"
  | .lendingPoolSolvency      => "defi.lending_pool_solvency"
  | .liquidationCorrectness   => "defi.liquidation_correctness"
  | .interestRateModelCorrectness => "defi.interest_rate_model_correctness"
  | .stakingRewardsDistribution => "defi.staking_rewards_distribution"
  | .perpetualFundingRate     => "defi.perpetual_funding_rate"
  | .evmSemantics             => "semantics.evm"
  | .soliditySemantics        => "semantics.solidity"
  | .vyperSemantics           => "semantics.vyper"
  | .moveSemantics            => "semantics.move"
  | .cairoSemantics           => "semantics.cairo"

def PropertyId.title : PropertyId → String
  | .reentrancyAbsence        => "Reentrancy Absence"
  | .integerOverflowUnderflow => "Integer Overflow/Underflow"
  | .accessControlCorrectness => "Access Control Correctness"
  | .frontRunningResistance   => "Front-Running Resistance"
  | .flashLoanResistance      => "Flash Loan Attack Resistance"
  | .oracleManipulationResistance => "Oracle Manipulation Resistance"
  | .erc20Correctness         => "ERC-20 Token Standard"
  | .erc721Correctness        => "ERC-721 NFT Standard"
  | .erc1155Correctness       => "ERC-1155 Multi-Token"
  | .erc4626Correctness       => "ERC-4626 Vault Standard"
  | .governorContractsCorrectness => "Governor Contracts"
  | .ammConstantProduct       => "AMM Constant Product"
  | .ammArbitrageOptimality   => "AMM Arbitrage Optimality"
  | .lendingPoolSolvency      => "Lending Pool Solvency"
  | .liquidationCorrectness   => "Liquidation Correctness"
  | .interestRateModelCorrectness => "Interest Rate Model"
  | .stakingRewardsDistribution => "Staking Rewards Distribution"
  | .perpetualFundingRate     => "Perpetual Funding Rate"
  | .evmSemantics             => "EVM Semantics"
  | .soliditySemantics        => "Solidity Semantics"
  | .vyperSemantics           => "Vyper Semantics"
  | .moveSemantics            => "Move Semantics"
  | .cairoSemantics           => "Cairo Semantics"

def PropertyId.description : PropertyId → String
  | .reentrancyAbsence =>
      "Contracts are free from reentrant call vulnerabilities."
  | .integerOverflowUnderflow =>
      "Arithmetic operations are safe from overflow and underflow."
  | .accessControlCorrectness =>
      "Only authorized callers can execute privileged functions."
  | .frontRunningResistance =>
      "Transaction ordering cannot be exploited for guaranteed profit."
  | .flashLoanResistance =>
      "Single-transaction flash-loan attacks cannot break protocol invariants."
  | .oracleManipulationResistance =>
      "On-chain price feeds cannot be profitably manipulated."
  | .erc20Correctness =>
      "ERC-20 token state transitions respect the standard invariants."
  | .erc721Correctness =>
      "ERC-721 non-fungible token ownership and transfer rules are correct."
  | .erc1155Correctness =>
      "ERC-1155 batch operations preserve balance invariants."
  | .erc4626Correctness =>
      "ERC-4626 vault accounting for deposits and withdrawals is correct."
  | .governorContractsCorrectness =>
      "Governor-style contracts correctly implement voting and execution logic."
  | .ammConstantProduct =>
      "Automated market maker trades preserve the x*y=k invariant."
  | .ammArbitrageOptimality =>
      "Optimal AMM swaps can be derived from the invariant and fee model."
  | .lendingPoolSolvency =>
      "Outstanding borrows are bounded by collateralized deposits."
  | .liquidationCorrectness =>
      "Undercollateralized positions can be liquidated according to rules."
  | .interestRateModelCorrectness =>
      "Interest rates are computed correctly from utilization parameters."
  | .stakingRewardsDistribution =>
      "Staking rewards are distributed proportionally to stake/participation."
  | .perpetualFundingRate =>
      "Perpetual swap funding drives the mark price towards the index."
  | .evmSemantics =>
      "A complete formal specification of the Ethereum Virtual Machine."
  | .soliditySemantics =>
      "Denotational and/or operational semantics for Solidity."
  | .vyperSemantics =>
      "A formal model of the Vyper smart-contract language."
  | .moveSemantics =>
      "A formal model of the Move VM (Aptos/Sui)."
  | .cairoSemantics =>
      "A formal specification of the Cairo/StarkNet VM."

def PropertyId.toExpr (p : PropertyId) : Expr :=
  Expr.atom p.slug

end Spec
end Contracts
end Blockchain
end HeytingLean

