import HeytingLean.Noneism.ProofTheory.Completeness.RoutleyMeyerCore

namespace HeytingLean
namespace Noneism
namespace RM

open Noneism Formula

theorem rm_completeness {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact NDRMSyntax.completeness h

theorem rm_core_completeness {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact NDRMSyntax.completeness_core h

theorem rm_core_completeness_from_countermodel {σ : Type} [HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_from_countermodel h

theorem rm_completeness_from_countermodel {σ : Type} [HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact rm_completeness h

theorem rm_completeness_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact rm_completeness h

theorem rm_completeness_from_prime_truth_model_via_obligations
    {σ : Type}
    [HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : HasPrimeTheoryTruthObligations σ := primeTruthObligationsOfModel (σ := σ)
  intro h
  exact rm_completeness h

theorem rm_completeness_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligations σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact rm_completeness h

theorem rm_completeness_from_prime_truth_lift
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact rm_completeness h

theorem rm_completeness_from_modelProp_lift
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact rm_completeness_from_countermodel h

theorem rm_adequacy_from_prime_truth_lift
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_prime_truth_model

theorem rm_adequacy_from_modelProp_lift
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_countermodel

theorem rm_completeness_from_modelProp_split
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryNegImpLift σ P]
    [HasPrimeTheoryQuantifierLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact rm_completeness_from_modelProp_lift h

theorem rm_adequacy_from_modelProp_split
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryNegImpLift σ P]
    [HasPrimeTheoryQuantifierLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_modelProp_lift

theorem rm_completeness_from_star_transfer_lift_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : HasCanonicalStarTransferTruthBySize σ :=
    canonicalStarTransfer_truthBySize_of_truthLift (σ := σ)
  exact rm_completeness

theorem rm_adequacy_from_star_transfer_lift_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : HasCanonicalStarTransferTruthBySize σ :=
    canonicalStarTransfer_truthBySize_of_truthLift (σ := σ)
  exact rm_adequacy_from_countermodel

theorem rm_completeness_from_star_maximalMixedPrimeRealization_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_completeness_from_star_transfer_lift_and_truth_lift

theorem rm_core_completeness_from_star_maximalMixedPrimeRealization_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  cases rm_completeness_from_star_maximalMixedPrimeRealization_and_truth_lift
      (Γ := Γ) (φ := φ) h with
  | core hCore =>
      exact hCore

theorem rm_adequacy_from_star_maximalMixedPrimeRealization_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_adequacy_from_star_transfer_lift_and_truth_lift

theorem rm_completeness_from_star_maximalMixedPrimeRealization_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_completeness

theorem rm_core_completeness_from_star_maximalMixedPrimeRealization_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  cases rm_completeness_from_star_maximalMixedPrimeRealization_and_truthBySize
      (Γ := Γ) (φ := φ) h with
  | core hCore =>
      exact hCore

theorem rm_adequacy_from_star_maximalMixedPrimeRealization_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_adequacy_from_countermodel

theorem rm_completeness_from_star_maximalMixed_split_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ := inferInstance
  exact rm_completeness_from_star_transfer_lift_and_truth_lift

theorem rm_core_completeness_from_star_maximalMixed_split_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  cases rm_completeness_from_star_maximalMixed_split_and_truth_lift
      (Γ := Γ) (φ := φ) h with
  | core hCore =>
      exact hCore

theorem rm_adequacy_from_star_maximalMixed_split_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ := inferInstance
  exact rm_adequacy_from_star_transfer_lift_and_truth_lift

theorem rm_completeness_from_star_maximalMixed_split_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ := inferInstance
  exact rm_completeness

theorem rm_core_completeness_from_star_maximalMixed_split_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  cases rm_completeness_from_star_maximalMixed_split_and_truthBySize
      (Γ := Γ) (φ := φ) h with
  | core hCore =>
      exact hCore

theorem rm_adequacy_from_star_maximalMixed_split_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ := inferInstance
  exact rm_adequacy_from_countermodel

theorem rm_completeness_from_star_maximalMixedTransferRealization_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_completeness_from_star_transfer_lift_and_truth_lift

theorem rm_core_completeness_from_star_maximalMixedTransferRealization_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  cases rm_completeness_from_star_maximalMixedTransferRealization_and_truth_lift
      (Γ := Γ) (φ := φ) h with
  | core hCore =>
      exact hCore

theorem rm_adequacy_from_star_maximalMixedTransferRealization_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_adequacy_from_star_transfer_lift_and_truth_lift

theorem rm_completeness_from_star_maximalMixedTransferRealization_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_completeness

theorem rm_core_completeness_from_star_maximalMixedTransferRealization_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  cases rm_completeness_from_star_maximalMixedTransferRealization_and_truthBySize
      (Γ := Γ) (φ := φ) h with
  | core hCore =>
      exact hCore

theorem rm_adequacy_from_star_maximalMixedTransferRealization_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_adequacy_from_countermodel

theorem rm_completeness_from_star_maximalMixed_leftIn_rightOut_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  exact rm_completeness_from_star_maximalMixedTransferRealization_and_truth_lift

theorem rm_core_completeness_from_star_maximalMixed_leftIn_rightOut_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  cases rm_completeness_from_star_maximalMixed_leftIn_rightOut_and_truth_lift
      (Γ := Γ) (φ := φ) h with
  | core hCore =>
      exact hCore

theorem rm_adequacy_from_star_maximalMixed_leftIn_rightOut_and_truth_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  exact rm_adequacy_from_star_maximalMixedTransferRealization_and_truth_lift

theorem rm_completeness_from_star_maximalMixed_leftIn_rightOut_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  exact rm_completeness_from_star_maximalMixedTransferRealization_and_truthBySize

theorem rm_core_completeness_from_star_maximalMixed_leftIn_rightOut_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  cases rm_completeness_from_star_maximalMixed_leftIn_rightOut_and_truthBySize
      (Γ := Γ) (φ := φ) h with
  | core hCore =>
      exact hCore

theorem rm_adequacy_from_star_maximalMixed_leftIn_rightOut_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  exact rm_adequacy_from_star_maximalMixedTransferRealization_and_truthBySize

theorem rm_completeness_from_canonicalStarTransferSplit
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferNegImpLift σ]
    [HasCanonicalStarTransferQuantifierLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  rm_completeness

theorem rm_adequacy_from_canonicalStarTransferSplit
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferNegImpLift σ]
    [HasCanonicalStarTransferQuantifierLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_countermodel

theorem rm_completeness_from_canonicalStarTransferTruthLift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  rm_completeness

theorem rm_adequacy_from_canonicalStarTransferTruthLift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_countermodel

theorem rm_completeness_from_canonicalStarTransferTruthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  rm_completeness

theorem rm_adequacy_from_canonicalStarTransferTruthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_countermodel

theorem rm_adequacy_from_prime_truth_model_via_lift_explicit
    {σ : Type}
    [HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  let P : HasPrimeTheoryTruthModelProp σ := primeTruthModelPropOfModel σ
  letI : HasPrimeTheoryTruthModelProp σ := P
  letI : HasPrimeTheoryTruthLift σ P := primeTruthLift_of_model_explicit (σ := σ)
  exact rm_adequacy_from_prime_truth_lift

theorem rm_core_completeness_prop_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_prime_truth_model_via_obligations
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  adequacy_prop_from_prime_truth_obligations (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_prime_truth_model_via_canonical_prime_rel
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_prime_truth_model_via_canonical_prime_rel (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_core_completeness_prop_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_prime_truth_obligations (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_prime_truth_obligations (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_prime_truth_obligations (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_core_completeness_prop_from_canonical_prime_rel
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_canonical_prime_rel_via_star_seed_lift
    (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_core_completeness_prop_from_canonical_prime_rel_via_star_seed_lift
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_canonical_prime_rel_via_star_seed_lift
    (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_canonical_prime_rel
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_canonical_prime_rel_via_star_seed_lift
    (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_canonical_prime_rel_via_star_seed_lift
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_canonical_prime_rel_via_star_seed_lift
    (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_canonical_prime_rel
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_canonical_prime_rel_via_star_seed_lift
    (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_canonical_prime_rel_via_star_seed_lift
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_canonical_prime_rel_via_star_seed_lift
    (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_core_completeness_prop_from_star_imp
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_star_imp (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_star_imp
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_star_imp (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_star_imp
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_star_imp (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_core_completeness_prop_from_star_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_star_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_star_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_core_completeness_prop_from_star_maximalMixedPrimeRealization
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_star_maximalMixedPrimeRealization
    (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_star_maximalMixedPrimeRealization
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_star_maximalMixedPrimeRealization
    (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_star_maximalMixedPrimeRealization
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_star_maximalMixedPrimeRealization
    (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_core_completeness_prop_from_star_seed_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_star_seed_lift (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_star_seed_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_star_seed_lift (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_star_seed_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_star_seed_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_core_completeness_prop_from_star_transfer_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_star_transfer_lift (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_star_transfer_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_star_transfer_lift (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_star_transfer_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_star_transfer_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_core_completeness_prop_from_star_reflection_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_star_reflection_lift (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_star_reflection_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_star_reflection_lift (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_star_reflection_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_star_reflection_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_star_seed_lift_of_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_star_seed_lift_of_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_core_completeness_prop_from_star_exists_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro h
  exact core_completeness_prop_from_star_exists_counterexample (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_completeness_prop_from_star_exists_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro h
  exact completeness_prop_from_star_exists_counterexample (Γ := Γ) (φ := φ) hΓ hφ h

theorem rm_adequacy_prop_from_star_exists_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  exact adequacy_prop_from_star_exists_counterexample (Γ := Γ) (φ := φ) hΓ hφ

end RM
end Noneism
end HeytingLean
