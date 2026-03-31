import HeytingLean.Noneism.ProofTheory.Soundness.RoutleyMeyer
import HeytingLean.Noneism.ProofTheory.Completeness.RoutleyMeyerHenkin
import HeytingLean.Noneism.ProofTheory.RMSeq

namespace HeytingLean
namespace Noneism
namespace RM

open Noneism Formula

theorem rm_adequacy_ndsyntax {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  constructor
  · exact rm_soundness
  · exact rm_completeness

/--
Closed adequacy for the baseline RM derivability surface `NDRM.Derives`.

This theorem is assumption-free and tracks semantic consequence definitionally.
-/
theorem rm_adequacy {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ ↔ Entails Γ φ :=
  NDRM.derives_iff_entails (Γ := Γ) (φ := φ)

theorem rm_adequacy_closed {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy

/-- Primary public adequacy route for the baseline RM calculus (`NDRM.Derives`). -/
theorem rm_adequacy_primary_closed {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_closed_ndrm

theorem rmseq_adequacy {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.Derives (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  RMSeq.derives_fromCore_iff_entails (Γ := Γ) (φ := φ)

theorem rmseq_nd_equiv {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.Derives (RMSeq.fromCore Γ φ) ↔ NDRMSyntax.Derives Γ φ :=
  RMSeq.seq_nd_equiv (Γ := Γ) (φ := φ)

theorem rmseq_syn_adequacy {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  RMSeq.derivesSyn_fromCore_iff_entails (Γ := Γ) (φ := φ)

theorem rmseq_syn_nd_equiv {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ NDRMSyntax.Derives Γ φ :=
  RMSeq.derivesSyn_fromCore_iff_nd (Γ := Γ) (φ := φ)

theorem rmseq_syn_adequacy_from_seqclass {σ : Type} [RMSeq.HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  RMSeq.derivesSyn_fromCore_iff_entails_of_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_seqclass {σ : Type} [RMSeq.HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : NDRMSyntax.HasCoreCompleteness σ := RMSeq.coreCompleteness_of_seqSynCompleteness σ
  exact rm_adequacy_ndsyntax

/--
Fallback adequacy route for the syntax calculus via seqclass completeness.

This is intentionally kept as a named alias to make primary-vs-fallback routing explicit.
-/
theorem rm_adequacy_fallback_seqclass {σ : Type} [RMSeq.HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_seqclass

/--
Parity witness: under seqclass completeness, the seqclass fallback and the induced ND-syntax
adequacy route expose extensionally equal forward/backward maps.
-/
theorem rm_adequacy_from_seqclass_route_parity
    {σ : Type} [RMSeq.HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    ((rm_adequacy_from_seqclass (σ := σ) (Γ := Γ) (φ := φ)).1 =
      (by
        letI : NDRMSyntax.HasCoreCompleteness σ := RMSeq.coreCompleteness_of_seqSynCompleteness σ
        exact (rm_adequacy_ndsyntax (σ := σ) (Γ := Γ) (φ := φ)).1)) ∧
    ((rm_adequacy_from_seqclass (σ := σ) (Γ := Γ) (φ := φ)).2 =
      (by
        letI : NDRMSyntax.HasCoreCompleteness σ := RMSeq.coreCompleteness_of_seqSynCompleteness σ
        exact (rm_adequacy_ndsyntax (σ := σ) (Γ := Γ) (φ := φ)).2)) := by
  constructor <;> exact Subsingleton.elim _ _

theorem rmseq_syn_adequacy_prop_from_seqclass
    {σ : Type} [RMSeq.HasFromCoreSeqCompletenessProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  RMSeq.derivesSyn_fromCore_iff_entails_prop_of_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_seqclass
    {σ : Type} [RMSeq.HasFromCoreSeqCompletenessProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  constructor
  · exact rm_soundness
  · intro hEnt
    have hSyn :
        RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) :=
      (rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ).2 hEnt
    exact NDRMSyntax.Derives.core
      ((RMSeq.derivesSyn_fromCore_iff_core (Γ := Γ) (φ := φ)).1 hSyn)

instance hasFromCoreSeqCompleteness_of_countermodel
    (σ : Type) [HasCoreCountermodel σ] :
    RMSeq.HasFromCoreSeqCompleteness σ where
  complete := by
    classical
    intro Γ φ hValid
    have hEnt : Entails Γ φ :=
      (RMSeq.valid_fromCore_iff_entails (Γ := Γ) (φ := φ)).1 hValid
    by_cases hSyn : RMSeq.DerivesSyn (RMSeq.fromCore Γ φ)
    · exact hSyn
    · have hNotCore : ¬ NDRMSyntax.DerivesCore Γ φ := by
        intro hCore
        exact hSyn ((RMSeq.derivesSyn_fromCore_iff_core (Γ := Γ) (φ := φ)).2 hCore)
      rcases HasCoreCountermodel.countermodel (σ := σ) hNotCore with
        ⟨W, D, M, ρ, w, hPrem, hNotSat⟩
      exact False.elim (hNotSat (hEnt W D M ρ w hPrem))

instance hasFromCoreSeqCompleteness_of_star_transfer_lift_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    RMSeq.HasFromCoreSeqCompleteness σ := by
  letI : HasCanonicalStarTransferTruthBySize σ :=
    canonicalStarTransfer_truthBySize_of_truthLift (σ := σ)
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_of_canonicalStarTransferTruthBySize (σ := σ)
  exact hasFromCoreSeqCompleteness_of_countermodel (σ := σ)

instance hasFromCoreSeqCompleteness_of_canonicalStarTransferSplit
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferNegImpLift σ]
    [HasCanonicalStarTransferQuantifierLift σ] :
    RMSeq.HasFromCoreSeqCompleteness σ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_of_canonicalStarTransferSplit (σ := σ)
  exact hasFromCoreSeqCompleteness_of_countermodel (σ := σ)

instance hasFromCoreSeqCompleteness_of_canonicalStarTransferTruthLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthLift σ] :
    RMSeq.HasFromCoreSeqCompleteness σ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_of_canonicalStarTransferTruthLift (σ := σ)
  exact hasFromCoreSeqCompleteness_of_countermodel (σ := σ)

instance hasFromCoreSeqCompleteness_of_canonicalStarTransferTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    RMSeq.HasFromCoreSeqCompleteness σ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_of_canonicalStarTransferTruthBySize (σ := σ)
  exact hasFromCoreSeqCompleteness_of_countermodel (σ := σ)

theorem rmseq_syn_adequacy_from_countermodel
    {σ : Type} [HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  rmseq_syn_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_countermodel_via_seqclass
    {σ : Type} [HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_henkin_from_henkinCountermodel_via_seqclass
    {σ : Type} [HasHenkinCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : HasCoreCountermodel σ := inferInstance
  exact rm_adequacy_from_countermodel_via_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_henkin_from_star_maximalMixed_henkinTruthBySize_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasStarMaximalMixedHenkinTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_from_star_maximalMixed_henkinTruthBySize (σ := σ)
  exact rm_adequacy_from_countermodel_via_seqclass (Γ := Γ) (φ := φ)

theorem rm_not_derives_of_not_entails
    {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ}
    (hNotEnt : ¬ Entails Γ φ) :
    ¬ NDRMSyntax.Derives Γ φ := by
  intro hDer
  exact hNotEnt (rm_soundness hDer)

theorem rm_not_derivesCore_of_not_entails
    {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ}
    (hNotEnt : ¬ Entails Γ φ) :
    ¬ NDRMSyntax.DerivesCore Γ φ := by
  intro hDer
  exact hNotEnt (rm_core_soundness hDer)

theorem rmseq_not_derivesSyn_from_countermodel
    {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ}
    (hCM :
      ∃ (W D : Type) (M : RM.Model σ W D) (ρ : RM.Valuation D) (w : W),
        (∀ ψ ∈ Γ, RM.sat M ρ w ψ) ∧ ¬ RM.sat M ρ w φ) :
    ¬ RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hSyn
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    (RMSeq.derivesSyn_fromCore_iff_core (Γ := Γ) (φ := φ)).1 hSyn
  exact rm_not_derivesCore_of_countermodel (Γ := Γ) (φ := φ) hCM hCore

theorem rmseq_not_derivesSyn_of_not_entails
    {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ}
    (hNotEnt : ¬ Entails Γ φ) :
    ¬ RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hSyn
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    (RMSeq.derivesSyn_fromCore_iff_core (Γ := Γ) (φ := φ)).1 hSyn
  exact rm_not_derivesCore_of_not_entails (Γ := Γ) (φ := φ) hNotEnt hCore

theorem rm_adequacy_from_prime_truth_model_via_seqclass
    {σ : Type} [HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_countermodel_via_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_prime_truth_obligations_via_seqclass
    {σ : Type} [HasPrimeTheoryTruthObligations σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_prime_truth_model_via_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_prime_truth_lift_via_seqclass
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_modelProp_lift_via_seqclass
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_modelProp_split_via_seqclass
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryNegImpLift σ P]
    [HasPrimeTheoryQuantifierLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_modelProp_lift_via_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_star_transfer_lift_and_truth_lift_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : HasCanonicalStarTransferTruthBySize σ :=
    canonicalStarTransfer_truthBySize_of_truthLift (σ := σ)
  exact rm_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_star_maximalMixedPrimeRealization_and_truth_lift_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_adequacy_from_star_transfer_lift_and_truth_lift_via_seqclass

theorem rm_adequacy_from_star_maximalMixedPrimeRealization_and_truthBySize_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_star_maximalMixedTransferRealization_and_truth_lift_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_adequacy_from_star_transfer_lift_and_truth_lift_via_seqclass

theorem rm_adequacy_from_star_maximalMixedTransferRealization_and_truthBySize_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact rm_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_star_maximalMixed_leftIn_rightOut_and_truth_lift_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  exact rm_adequacy_from_star_maximalMixedTransferRealization_and_truth_lift_via_seqclass

theorem rm_adequacy_from_star_maximalMixed_leftIn_rightOut_and_truthBySize_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  exact rm_adequacy_from_star_maximalMixedTransferRealization_and_truthBySize_via_seqclass

theorem rm_adequacy_from_canonicalStarTransferSplit_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferNegImpLift σ]
    [HasCanonicalStarTransferQuantifierLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_canonicalStarTransferTruthLift_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_canonicalStarTransferTruthBySize_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_from_seqclass (Γ := Γ) (φ := φ)

theorem rm_adequacy_from_prime_truth_model_via_lift_explicit_seqclass
    {σ : Type}
    [HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  let P : HasPrimeTheoryTruthModelProp σ := primeTruthModelPropOfModel σ
  letI : HasPrimeTheoryTruthModelProp σ := P
  letI : HasPrimeTheoryTruthLift σ P := primeTruthLift_of_model_explicit (σ := σ)
  exact rm_adequacy_from_prime_truth_lift_via_seqclass (Γ := Γ) (φ := φ)

theorem rmseq_syn_adequacy_prop_from_countermodel_via_seqclass
    {σ : Type} [HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_countermodel_via_seqclass
    {σ : Type} [HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_adequacy_prop_from_prime_truth_lift_via_seqclass
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_prime_truth_lift_via_seqclass
    {σ : Type}
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_prime_truth_model_via_lift_explicit_seqclass
    {σ : Type}
    [HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ := by
  let P : HasPrimeTheoryTruthModelProp σ := primeTruthModelPropOfModel σ
  letI : HasPrimeTheoryTruthModelProp σ := P
  letI : HasPrimeTheoryTruthLift σ P := primeTruthLift_of_model_explicit (σ := σ)
  exact rm_adequacy_prop_from_prime_truth_lift_via_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_adequacy_prop_from_prime_truth_model_full_via_seqclass
    {σ : Type} [HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_prime_truth_model_full_via_seqclass
    {σ : Type} [HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_adequacy_prop_from_prime_truth_obligations_full_via_seqclass
    {σ : Type} [HasPrimeTheoryTruthObligations σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_prime_truth_obligations_full_via_seqclass
    {σ : Type} [HasPrimeTheoryTruthObligations σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_completeness_prop_from_canonical_prime_rel
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    rm_core_completeness_prop_from_canonical_prime_rel_via_star_seed_lift
      (Γ := Γ) (φ := φ) hΓ hφ hEnt
  exact RMSeq.derivesSyn_of_nd hCore

theorem rmseq_syn_completeness_prop_from_canonical_prime_rel_via_star_seed_lift
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  exact rmseq_syn_completeness_prop_from_canonical_prime_rel
    (Γ := Γ) (φ := φ) hΓ hφ hEnt

theorem rmseq_syn_adequacy_prop_from_canonical_prime_rel
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ := by
  letI : RMSeq.HasFromCoreSeqCompletenessProp σ := {
    complete := by
      intro Γ φ hΓ hφ hEnt
      exact rmseq_syn_completeness_prop_from_canonical_prime_rel
        (Γ := Γ) (φ := φ) hΓ hφ hEnt
  }
  exact rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_completeness_prop_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    rm_core_completeness_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ hEnt
  exact RMSeq.derivesSyn_of_nd hCore

theorem rmseq_syn_adequacy_prop_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ := by
  letI : RMSeq.HasFromCoreSeqCompletenessProp σ := {
    complete := by
      intro Γ φ hΓ hφ hEnt
      exact rmseq_syn_completeness_prop_from_prime_truth_model
        (Γ := Γ) (φ := φ) hΓ hφ hEnt
  }
  exact rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_adequacy_prop_from_prime_truth_model_via_obligations
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  rmseq_syn_adequacy_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_adequacy_prop_from_prime_truth_model_via_canonical_prime_rel
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  rmseq_syn_adequacy_prop_from_canonical_prime_rel (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_completeness_prop_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    rm_core_completeness_prop_from_prime_truth_obligations (Γ := Γ) (φ := φ) hΓ hφ hEnt
  exact RMSeq.derivesSyn_of_nd hCore

theorem rmseq_syn_adequacy_prop_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ := by
  letI : RMSeq.HasFromCoreSeqCompletenessProp σ := {
    complete := by
      intro Γ φ hΓ hφ hEnt
      exact rmseq_syn_completeness_prop_from_prime_truth_obligations
        (Γ := Γ) (φ := φ) hΓ hφ hEnt
  }
  exact rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_completeness_prop_from_star_imp
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    rm_core_completeness_prop_from_star_imp (Γ := Γ) (φ := φ) hΓ hφ hEnt
  exact RMSeq.derivesSyn_of_nd hCore

theorem rmseq_syn_adequacy_prop_from_star_imp
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ := by
  letI : RMSeq.HasFromCoreSeqCompletenessProp σ := {
    complete := by
      intro Γ φ hΓ hφ hEnt
      exact rmseq_syn_completeness_prop_from_star_imp
        (Γ := Γ) (φ := φ) hΓ hφ hEnt
  }
  exact rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_completeness_prop_from_star_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    rm_core_completeness_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ hEnt
  exact RMSeq.derivesSyn_of_nd hCore

theorem rmseq_syn_adequacy_prop_from_star_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ := by
  letI : RMSeq.HasFromCoreSeqCompletenessProp σ := {
    complete := by
      intro Γ φ hΓ hφ hEnt
      exact rmseq_syn_completeness_prop_from_star_counterexample
        (Γ := Γ) (φ := φ) hΓ hφ hEnt
  }
  exact rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_completeness_prop_from_star_maximalMixedPrimeRealization
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    rm_core_completeness_prop_from_star_maximalMixedPrimeRealization
      (Γ := Γ) (φ := φ) hΓ hφ hEnt
  exact RMSeq.derivesSyn_of_nd hCore

theorem rmseq_syn_adequacy_prop_from_star_maximalMixedPrimeRealization
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ := by
  letI : RMSeq.HasFromCoreSeqCompletenessProp σ := {
    complete := by
      intro Γ φ hΓ hφ hEnt
      exact rmseq_syn_completeness_prop_from_star_maximalMixedPrimeRealization
        (Γ := Γ) (φ := φ) hΓ hφ hEnt
  }
  exact rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_completeness_prop_from_star_exists_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    rm_core_completeness_prop_from_star_exists_counterexample (Γ := Γ) (φ := φ) hΓ hφ hEnt
  exact RMSeq.derivesSyn_of_nd hCore

theorem rmseq_syn_completeness_prop_from_star_reflection_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    rm_core_completeness_prop_from_star_reflection_lift (Γ := Γ) (φ := φ) hΓ hφ hEnt
  exact RMSeq.derivesSyn_of_nd hCore

theorem rmseq_syn_completeness_prop_from_star_transfer_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) := by
  intro hEnt
  have hCore : NDRMSyntax.DerivesCore Γ φ :=
    rm_core_completeness_prop_from_star_transfer_lift (Γ := Γ) (φ := φ) hΓ hφ hEnt
  exact RMSeq.derivesSyn_of_nd hCore

theorem rmseq_syn_adequacy_prop_from_star_reflection_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ := by
  letI : RMSeq.HasFromCoreSeqCompletenessProp σ := {
    complete := by
      intro Γ φ hΓ hφ hEnt
      exact rmseq_syn_completeness_prop_from_star_reflection_lift
        (Γ := Γ) (φ := φ) hΓ hφ hEnt
  }
  exact rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_adequacy_prop_from_star_transfer_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ := by
  letI : RMSeq.HasFromCoreSeqCompletenessProp σ := {
    complete := by
      intro Γ φ hΓ hφ hEnt
      exact rmseq_syn_completeness_prop_from_star_transfer_lift
        (Γ := Γ) (φ := φ) hΓ hφ hEnt
  }
  exact rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_adequacy_prop_from_star_exists_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ := by
  letI : RMSeq.HasFromCoreSeqCompletenessProp σ := {
    complete := by
      intro Γ φ hΓ hφ hEnt
      exact rmseq_syn_completeness_prop_from_star_exists_counterexample
        (Γ := Γ) (φ := φ) hΓ hφ hEnt
  }
  exact rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

instance hasFromCoreSeqCompletenessProp_of_canonical_prime_rel
    (σ : Type) [HasCanonicalPrimeRelProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_canonical_prime_rel_via_star_seed_lift
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

instance hasFromCoreSeqCompletenessProp_of_prime_truth_model
    (σ : Type) [HasPrimeTheoryTruthModelProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_prime_truth_model
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

instance hasFromCoreSeqCompletenessProp_of_prime_truth_obligations
    (σ : Type) [HasPrimeTheoryTruthObligationsProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_prime_truth_obligations
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

instance hasFromCoreSeqCompletenessProp_of_star_imp
    (σ : Type)
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_star_imp
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

instance hasFromCoreSeqCompletenessProp_of_star_counterexample
    (σ : Type)
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_star_counterexample
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

instance hasFromCoreSeqCompletenessProp_of_star_maximalMixedPrimeRealization
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_star_maximalMixedPrimeRealization
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

instance hasFromCoreSeqCompletenessProp_of_star_seed_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeLift σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_star_counterexample
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

instance hasFromCoreSeqCompletenessProp_of_star_reflection_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_star_reflection_lift
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

instance hasFromCoreSeqCompletenessProp_of_star_transfer_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_star_transfer_lift
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

instance hasFromCoreSeqCompletenessProp_of_star_exists_counterexample
    (σ : Type)
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact rmseq_syn_completeness_prop_from_star_exists_counterexample
      (Γ := Γ) (φ := φ) hΓ hφ hEnt

theorem rm_adequacy_prop_from_canonical_prime_rel_via_seqclass
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_canonical_prime_rel_via_star_seed_lift_via_seqclass
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_prime_truth_model_via_seqclass
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_prime_truth_obligations_via_seqclass
    {σ : Type}
    [HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_star_imp_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_star_counterexample_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_star_maximalMixedPrimeRealization_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rmseq_syn_adequacy_prop_from_star_maximalMixedPrimeRealization_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ Entails Γ φ :=
  rmseq_syn_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_star_seed_lift_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_star_reflection_lift_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_star_transfer_lift_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

theorem rm_adequacy_prop_from_star_exists_counterexample_via_seqclass
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ Entails Γ φ :=
  rm_adequacy_prop_from_seqclass (Γ := Γ) (φ := φ) hΓ hφ

end RM
end Noneism
end HeytingLean
