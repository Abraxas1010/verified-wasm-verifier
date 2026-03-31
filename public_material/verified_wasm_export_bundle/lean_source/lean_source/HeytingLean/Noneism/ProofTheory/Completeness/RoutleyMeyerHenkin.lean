import HeytingLean.Noneism.ProofTheory.Completeness.RoutleyMeyer

namespace HeytingLean
namespace Noneism
namespace RM

open Noneism Formula

/--
Focused FO countermodel interface for the RM Henkin lane.

This isolates the remaining constructive payload required to recover
`HasCoreCountermodel` (hence completeness/adequacy) without committing to a specific
canonical-model implementation in this module.
-/
class HasHenkinCoreCountermodel (σ : Type) : Prop where
  countermodel :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      ¬ NDRMSyntax.DerivesCore Γ φ →
        ∃ (W D : Type) (M : RM.Model σ W D) (ρ : RM.Valuation D) (w : W),
          (∀ ψ ∈ Γ, RM.sat M ρ w ψ) ∧ ¬ RM.sat M ρ w φ

instance hasCoreCountermodel_of_henkinCoreCountermodel
    (σ : Type) [HasHenkinCoreCountermodel σ] :
    HasCoreCountermodel σ where
  countermodel := HasHenkinCoreCountermodel.countermodel (σ := σ)

theorem hasHenkinCoreCountermodel_of_coreCountermodel
    (σ : Type) [HasCoreCountermodel σ] :
    HasHenkinCoreCountermodel σ := by
  refine ⟨?_⟩
  intro Γ φ hNot
  exact HasCoreCountermodel.countermodel (σ := σ) (Γ := Γ) (φ := φ) hNot

theorem hasCoreCompleteness_of_henkinCoreCountermodel
    (σ : Type) [HasHenkinCoreCountermodel σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : HasCoreCountermodel σ := inferInstance
  exact hasCoreCompleteness_from_countermodel σ

/--
Assumption-free Henkin countermodel lane.

Given a non-derivable core sequent, closed core completeness yields `¬ Entails`.
From `¬ Entails`, we extract a concrete semantic counterexample and package it as
`HasHenkinCoreCountermodel`.
-/
theorem hasHenkinCoreCountermodel_assumption_free
    (σ : Type) :
    HasHenkinCoreCountermodel σ := by
  refine ⟨?_⟩
  intro Γ φ hNotDer
  have hNotEnt : ¬ Entails Γ φ := by
    intro hEnt
    letI : NDRMSyntax.HasCoreCompleteness σ :=
      hasCoreCompleteness_assumption_free (σ := σ)
    exact hNotDer (NDRMSyntax.completeness_core hEnt)
  classical
  by_contra hNoCounterexample
  apply hNotEnt
  intro W D M ρ w hPrem
  by_contra hNotSat
  exact hNoCounterexample ⟨W, D, M, ρ, w, hPrem, hNotSat⟩

instance (priority := low) hasHenkinCoreCountermodel_assumption_free_inst
    (σ : Type) :
    HasHenkinCoreCountermodel σ :=
  hasHenkinCoreCountermodel_assumption_free (σ := σ)

/--
Packaged Henkin truth-by-size payload for the `star + maximalMixed` RM profile.

This gives a non-cyclic integration point for future constructive FO witness machinery:
provide this payload once, and the standard countermodel/completeness exports follow.
-/
class HasStarMaximalMixedHenkinTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ] : Prop where
  truthBySize : HasCanonicalStarTransferTruthBySize σ

instance hasStarMaximalMixedHenkinTruthBySize_of_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasStarMaximalMixedHenkinTruthBySize σ where
  truthBySize := inferInstance

theorem hasHenkinCoreCountermodel_from_star_maximalMixed_henkinTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasStarMaximalMixedHenkinTruthBySize σ] :
    HasHenkinCoreCountermodel σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  letI : HasCanonicalStarTransferTruthBySize σ :=
    (inferInstance : HasStarMaximalMixedHenkinTruthBySize σ).truthBySize
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_from_star_maximalMixedPrimeRealization_and_truthBySize (σ := σ)
  refine ⟨?_⟩
  intro Γ φ hNot
  exact HasCoreCountermodel.countermodel (σ := σ) (Γ := Γ) (φ := φ) hNot

instance hasHenkinCoreCountermodel_of_star_maximalMixed_henkinTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasStarMaximalMixedHenkinTruthBySize σ] :
    HasHenkinCoreCountermodel σ :=
  hasHenkinCoreCountermodel_from_star_maximalMixed_henkinTruthBySize (σ := σ)

theorem hasCoreCountermodel_from_star_maximalMixed_henkinTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasStarMaximalMixedHenkinTruthBySize σ] :
    HasCoreCountermodel σ := by
  letI : HasHenkinCoreCountermodel σ :=
    hasHenkinCoreCountermodel_from_star_maximalMixed_henkinTruthBySize (σ := σ)
  exact inferInstance

theorem hasCoreCompleteness_from_star_maximalMixed_henkinTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasStarMaximalMixedHenkinTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_from_star_maximalMixed_henkinTruthBySize (σ := σ)
  exact hasCoreCompleteness_from_countermodel σ

instance hasCoreCompleteness_of_star_maximalMixed_henkinTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasStarMaximalMixedHenkinTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_from_star_maximalMixed_henkinTruthBySize (σ := σ)
  exact hasCoreCompleteness_from_countermodel σ

/--
FO-level export for the current RM derivability surface.

At this stage, FO completeness is routed through the same `HasCoreCompleteness` interface as the
propositional RM core, while preserving theorem-name stability for downstream files.
-/
theorem rm_completeness_henkin {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  rm_completeness

theorem rm_adequacy_henkin {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  NDRMSyntax.adequacy

/-- Closed FO adequacy export for the Henkin lane. -/
theorem rm_adequacy_henkin_closed
    {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : HasHenkinCoreCountermodel σ :=
    hasHenkinCoreCountermodel_assumption_free (σ := σ)
  letI : NDRMSyntax.HasCoreCompleteness σ :=
    hasCoreCompleteness_of_henkinCoreCountermodel σ
  exact rm_adequacy_henkin

/-- Closed FO completeness export for the Henkin lane. -/
theorem rm_completeness_henkin_closed
    {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : HasHenkinCoreCountermodel σ :=
    hasHenkinCoreCountermodel_assumption_free (σ := σ)
  letI : NDRMSyntax.HasCoreCompleteness σ :=
    hasCoreCompleteness_of_henkinCoreCountermodel σ
  exact rm_completeness_henkin

theorem rm_completeness_henkin_from_henkinCountermodel
    {σ : Type} [HasHenkinCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : HasCoreCountermodel σ := inferInstance
  exact rm_completeness_from_countermodel

theorem rm_adequacy_henkin_from_henkinCountermodel
    {σ : Type} [HasHenkinCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : HasCoreCountermodel σ := inferInstance
  exact rm_adequacy_from_countermodel

theorem rm_completeness_henkin_from_star_maximalMixed_henkinTruthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasStarMaximalMixedHenkinTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_from_star_maximalMixed_henkinTruthBySize (σ := σ)
  exact rm_completeness_from_countermodel

theorem rm_adequacy_henkin_from_star_maximalMixed_henkinTruthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasStarMaximalMixedHenkinTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_from_star_maximalMixed_henkinTruthBySize (σ := σ)
  exact rm_adequacy_from_countermodel

/--
Concrete FO profile (without wrapper-class assumptions):
`HasCanonicalStarProp + HasMaximalMixedPrimeRealization + HasCanonicalStarTransferTruthBySize`
is sufficient for the Henkin countermodel interface.
-/
theorem hasHenkinCoreCountermodel_from_star_maximalMixedPrimeRealization_and_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasHenkinCoreCountermodel σ := by
  letI : HasStarMaximalMixedHenkinTruthBySize σ := inferInstance
  exact hasHenkinCoreCountermodel_from_star_maximalMixed_henkinTruthBySize (σ := σ)

theorem rm_completeness_henkin_from_star_maximalMixedPrimeRealization_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : HasHenkinCoreCountermodel σ :=
    hasHenkinCoreCountermodel_from_star_maximalMixedPrimeRealization_and_truthBySize (σ := σ)
  exact rm_completeness_henkin_from_henkinCountermodel

theorem rm_adequacy_henkin_from_star_maximalMixedPrimeRealization_and_truthBySize
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : HasHenkinCoreCountermodel σ :=
    hasHenkinCoreCountermodel_from_star_maximalMixedPrimeRealization_and_truthBySize (σ := σ)
  exact rm_adequacy_henkin_from_henkinCountermodel

end RM
end Noneism
end HeytingLean
