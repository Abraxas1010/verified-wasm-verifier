import HeytingLean.Blockchain.Contracts.Spec
import HeytingLean.Blockchain.Contracts.Model
import HeytingLean.DeFi.Model
import HeytingLean.DeFi.AMM

/-
# Blockchain.Contracts.DeFiBridge

Bridges between `Blockchain.Contracts.Spec.PropertyId` and the DeFi and
ERC-style models:

* `ammConstantProduct` and `ammArbitrageOptimality` are interpreted via
  `DeFi.AMM.ConstantProductStatement` and
  `DeFi.AMM.ArbitrageOptimalityStatement`;
* `lendingPoolSolvency` is realised by
  `DeFi.Lending.LendingSequenceSolvencyStatement`; and
* `erc20Correctness` is realised by
  `Blockchain.Contracts.Model.ERC20InvariantStatement`.

This keeps the mapping from spec identifiers to semantic statements
local and lightweight, without changing the global CCI registry.
-/

namespace HeytingLean
namespace Blockchain
namespace Contracts
namespace DeFiBridge

open HeytingLean.DeFi
open HeytingLean.Blockchain.Contracts

/-- Interpretation of contract/DeFi `PropertyId`s in terms of the
    concrete DeFi and ERC20 models currently implemented in this
    repository. Properties without a dedicated model yet are mapped to
    `True` defaults and will be refined as new modules are added. -/
def propertyHolds (p : Spec.PropertyId) : Prop :=
  match p with
  | .ammConstantProduct       => AMM.ConstantProductStatement
  | .ammArbitrageOptimality   => AMM.ArbitrageOptimalityStatement
  | .lendingPoolSolvency      => Lending.LendingSequenceSolvencyStatement
  | .liquidationCorrectness   => Lending.LiquidationCorrectnessStatement
  | .interestRateModelCorrectness => Lending.InterestRateModelStatement
  | .stakingRewardsDistribution => Lending.StakingRewardsStatement
  | .erc20Correctness         => Model.ERC20InvariantStatement
  | .reentrancyAbsence        => True
  | .integerOverflowUnderflow => True
  | .accessControlCorrectness => True
  | .frontRunningResistance   => True
  | .flashLoanResistance      => True
  | .oracleManipulationResistance => True
  | .erc721Correctness        => True
  | .erc1155Correctness       => True
  | .erc4626Correctness       => True
  | .governorContractsCorrectness => True
  | .perpetualFundingRate     => True
  | .evmSemantics             => True
  | .soliditySemantics        => True
  | .vyperSemantics           => True
  | .moveSemantics            => True
  | .cairoSemantics           => True

/-- The `ammConstantProduct` registry row holds in the abstract AMM
    model via `constantProductStatement_holds`. -/
theorem propertyHolds_ammConstantProduct :
    propertyHolds Spec.PropertyId.ammConstantProduct := by
  simpa [propertyHolds] using AMM.constantProductStatement_holds

/-- The `ammArbitrageOptimality` registry row holds in the detailed AMM
    model via `arbitrageOptimalityStatement_holds`. -/
theorem propertyHolds_ammArbitrageOptimality :
    propertyHolds Spec.PropertyId.ammArbitrageOptimality := by
  simpa [propertyHolds] using AMM.arbitrageOptimalityStatement_holds

/-- The `lendingPoolSolvency` registry row holds in the abstract
    lending model via `lendingSequenceSolvencyStatement_holds`. -/
theorem propertyHolds_lendingPoolSolvency :
    propertyHolds Spec.PropertyId.lendingPoolSolvency := by
  simpa [propertyHolds] using Lending.lendingSequenceSolvencyStatement_holds

/-- The `liquidationCorrectness` registry row holds in the abstract
    lending model via `liquidationCorrectnessStatement_holds`. -/
theorem propertyHolds_liquidationCorrectness :
    propertyHolds Spec.PropertyId.liquidationCorrectness := by
  simpa [propertyHolds] using Lending.liquidationCorrectnessStatement_holds

/-- The `erc20Correctness` registry row holds in the ERC20 model via
    `erc20InvariantStatement_holds`. -/
theorem propertyHolds_erc20Correctness :
    propertyHolds Spec.PropertyId.erc20Correctness := by
  simpa [propertyHolds] using Model.erc20InvariantStatement_holds

/-- The `interestRateModelCorrectness` registry row holds in the
    lending model via `interestRateModelStatement_holds`. -/
theorem propertyHolds_interestRateModelCorrectness :
    propertyHolds Spec.PropertyId.interestRateModelCorrectness := by
  simpa [propertyHolds] using Lending.interestRateModelStatement_holds

/-- The `stakingRewardsDistribution` registry row holds in the example
    staking-rewards model via `stakingRewardsStatement_holds`. -/
theorem propertyHolds_stakingRewardsDistribution :
    propertyHolds Spec.PropertyId.stakingRewardsDistribution := by
  simpa [propertyHolds] using Lending.stakingRewardsStatement_holds

end DeFiBridge
end Contracts
end Blockchain
end HeytingLean
