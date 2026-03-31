import HeytingLean.Noneism.ProofTheory.Completeness.RoutleyMeyerBridge

namespace HeytingLean
namespace Noneism
namespace Tests

open Noneism Formula

example {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ → RM.Entails Γ φ :=
  RM.rm_soundness

example {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ → RM.Entails Γ φ :=
  RM.rm_soundness_closed

example {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRM.Derives Γ φ :=
  RM.rm_completeness_closed

example {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_closed_ndrm

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    NDRMSyntax.DerivesCore Γ (.pi x φ) →
      NDRMSyntax.DerivesCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ) :=
  NDRMSyntax.core_piE ha

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    NDRMSyntax.DerivesCore Γ (.pi x φ) →
      NDRMSyntax.DerivesCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ) :=
  NDRMSyntax.core_piE_bound ha

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    NDRMSyntax.DerivesCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ) →
      NDRMSyntax.DerivesCore Γ (.sigma x φ) :=
  NDRMSyntax.core_sigmaI ha

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    NDRMSyntax.DerivesCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ) →
      NDRMSyntax.DerivesCore Γ (.sigma x φ) :=
  NDRMSyntax.core_sigmaI_bound ha

example {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    NDRMSyntax.DerivesCore Γ (.pi x φ) →
      NDRMSyntax.DerivesCore Γ φ :=
  NDRMSyntax.core_piE_self

example {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    NDRMSyntax.DerivesCore Γ φ →
      NDRMSyntax.DerivesCore Γ (.sigma x φ) :=
  NDRMSyntax.core_sigmaI_self

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    NDRMSyntax.Derives Γ (.pi x φ) →
      NDRMSyntax.Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) :=
  NDRMSyntax.piE ha

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    NDRMSyntax.Derives Γ (.pi x φ) →
      NDRMSyntax.Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) :=
  NDRMSyntax.piE_bound ha

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    NDRMSyntax.Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) →
      NDRMSyntax.Derives Γ (.sigma x φ) :=
  NDRMSyntax.sigmaI ha

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    NDRMSyntax.Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) →
      NDRMSyntax.Derives Γ (.sigma x φ) :=
  NDRMSyntax.sigmaI_bound ha

example {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    NDRMSyntax.Derives Γ (.pi x φ) →
      NDRMSyntax.Derives Γ φ :=
  NDRMSyntax.piE_self

example {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ →
      NDRMSyntax.Derives Γ (.sigma x φ) :=
  NDRMSyntax.sigmaI_self

example {σ : Type} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore [(.pi x φ)] (Syntax.substFormula (σ := σ) x (.var a) φ)) := by
  change RMSeq.DerivesSynL (NDRM.embedAtZero [(.pi x φ)])
    (.frm 0 (Syntax.substFormula (σ := σ) x (.var a) φ))
  refine RMSeq.DerivesSynL.piE ha ?_
  exact RMSeq.DerivesSynL.hyp (by simp [NDRM.embedAtZero])

example {σ : Type} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore [Syntax.substFormula (σ := σ) x (.var a) φ] (.sigma x φ)) := by
  change RMSeq.DerivesSynL (NDRM.embedAtZero [Syntax.substFormula (σ := σ) x (.var a) φ])
    (.frm 0 (.sigma x φ))
  refine RMSeq.DerivesSynL.sigmaI ha ?_
  exact RMSeq.DerivesSynL.hyp (by simp [NDRM.embedAtZero])

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ (.pi x φ)) →
      RMSeq.DerivesSyn (RMSeq.fromCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) :=
  RMSeq.derivesSyn_fromCore_piE ha

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ (.pi x φ)) →
      RMSeq.DerivesSyn (RMSeq.fromCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) :=
  RMSeq.derivesSyn_fromCore_piE_bound ha

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) →
      RMSeq.DerivesSyn (RMSeq.fromCore Γ (.sigma x φ)) :=
  RMSeq.derivesSyn_fromCore_sigmaI ha

example {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) →
      RMSeq.DerivesSyn (RMSeq.fromCore Γ (.sigma x φ)) :=
  RMSeq.derivesSyn_fromCore_sigmaI_bound ha

example {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ (.pi x φ)) →
      RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) :=
  RMSeq.derivesSyn_fromCore_piE_self

example {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) →
      RMSeq.DerivesSyn (RMSeq.fromCore Γ (.sigma x φ)) :=
  RMSeq.derivesSyn_fromCore_sigmaI_self

example {σ : Type} :
    NDRMSyntax.HasCoreCompleteness σ :=
  RM.hasCoreCompleteness_assumption_free (σ := σ)

example {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.core_completeness_assumption_free

example {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness

example {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_ndsyntax

example {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.Derives (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_adequacy

example {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_closed

example {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.Derives (RMSeq.fromCore Γ φ) ↔ NDRMSyntax.Derives Γ φ :=
  RM.rmseq_nd_equiv

example {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy

example {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ NDRMSyntax.Derives Γ φ :=
  RM.rmseq_syn_nd_equiv

example {σ : Type} [NDRMSyntax.HasCoreCompleteness σ] :
    RMSeq.HasFromCoreSeqCompleteness σ :=
  inferInstance

example {σ : Type} [RMSeq.HasFromCoreSeqCompleteness σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  RMSeq.coreCompleteness_of_seqSynCompleteness σ

example {σ : Type} [RMSeq.HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_from_seqclass

example {σ : Type} [RMSeq.HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_seqclass

example {σ : Type} [RM.HasCoreCountermodel σ] :
    RMSeq.HasFromCoreSeqCompleteness σ :=
  inferInstance

example {σ : Type} [RM.HasCoreCountermodel σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type} [RM.HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_from_countermodel

example {σ : Type} [RM.HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_countermodel_via_seqclass

example {σ : Type} [RM.HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_countermodel_via_seqclass hΓ hφ

example {σ : Type} [RM.HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_countermodel_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_prime_truth_model_via_seqclass

example {σ : Type}
    [RM.HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_prime_truth_model_full_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_model_full_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthObligations σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_prime_truth_obligations_via_seqclass

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_prime_truth_lift_via_seqclass

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_modelProp_lift_via_seqclass

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryNegImpLift σ P]
    [RM.HasPrimeTheoryQuantifierLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_modelProp_split_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_transfer_lift_and_truth_lift_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixedPrimeRealization_and_truth_lift_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixedPrimeRealization_and_truthBySize_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedTransferRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixedTransferRealization_and_truth_lift_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedTransferRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixedTransferRealization_and_truthBySize_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixed_leftIn_rightOut_and_truth_lift_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixed_leftIn_rightOut_and_truthBySize_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferNegImpLift σ]
    [RM.HasCanonicalStarTransferQuantifierLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_canonicalStarTransferSplit_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_canonicalStarTransferTruthLift_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_canonicalStarTransferTruthBySize_via_seqclass

example {σ : Type}
    [RM.HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_prime_truth_model_via_lift_explicit_seqclass

example {σ : Type}
    [RM.HasPrimeTheoryTruthObligations σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_prime_truth_obligations_full_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthObligations σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_obligations_full_via_seqclass hΓ hφ

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_prime_truth_lift_via_seqclass hΓ hφ

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_lift_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_model_via_lift_explicit_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_canonical_prime_rel hΓ hφ

example {σ : Type} [RMSeq.HasFromCoreSeqCompletenessProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_seqclass hΓ hφ

example {σ : Type} [RMSeq.HasFromCoreSeqCompletenessProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_seqclass hΓ hφ

example {σ : Type} [RM.HasCanonicalPrimeRelProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModelProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModel σ] :
    RM.HasPrimeTheoryTruthModelProp σ :=
  RM.primeTruthModelPropOfModel σ

example {σ : Type} [RM.HasPrimeTheoryTruthModel σ] :
    RM.HasCanonicalPrimeRelProp σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModelProp σ] :
    RM.HasPrimeTheoryTruthObligationsProp σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModelProp σ] :
    RM.HasCanonicalPrimeRelProp σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModelProp σ] :
    RM.HasCanonicalStarProp σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModelProp σ] :
    RM.HasCanonicalImpCounterexampleProp σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModelProp σ] :
    RM.CanonicalPair.HasPrimeTransferLift σ :=
  inferInstance

example {σ : Type} [P : RM.HasPrimeTheoryTruthModelProp σ] [RM.HasPrimeTheoryTruthLift σ P] :
    RM.HasPrimeTheoryTruthObligations σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModel σ] :
    @RM.HasPrimeTheoryTruthLift σ (RM.primeTruthModelPropOfModel σ) :=
  RM.primeTruthLift_of_model_explicit σ

example {σ : Type} [P : RM.HasPrimeTheoryTruthModelProp σ] [RM.HasPrimeTheoryTruthLift σ P] :
    RM.HasPrimeTheoryTruthModel σ :=
  inferInstance

example {σ : Type} [P : RM.HasPrimeTheoryTruthModelProp σ] [RM.HasPrimeTheoryTruthLift σ P] :
    RM.HasCoreCountermodel σ :=
  inferInstance

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryNegImpLift σ P]
    [RM.HasPrimeTheoryQuantifierLift σ P] :
    RM.HasPrimeTheoryTruthLift σ P :=
  inferInstance

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_modelProp_lift

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_modelProp_lift

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryNegImpLift σ P]
    [RM.HasPrimeTheoryQuantifierLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_modelProp_split

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryNegImpLift σ P]
    [RM.HasPrimeTheoryQuantifierLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_modelProp_split

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_star_transfer_lift_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_transfer_lift_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_from_star_maximalMixedPrimeRealization_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_star_maximalMixedPrimeRealization_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixedPrimeRealization_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_from_star_maximalMixedPrimeRealization_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_star_maximalMixedPrimeRealization_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixedPrimeRealization_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedTransferRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_from_star_maximalMixedTransferRealization_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedTransferRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_star_maximalMixedTransferRealization_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedTransferRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixedTransferRealization_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedTransferRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_from_star_maximalMixedTransferRealization_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedTransferRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_star_maximalMixedTransferRealization_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedTransferRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixedTransferRealization_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_from_star_maximalMixed_split_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_star_maximalMixed_split_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixed_split_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_from_star_maximalMixed_split_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_star_maximalMixed_split_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixed_split_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_from_star_maximalMixed_leftIn_rightOut_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_star_maximalMixed_leftIn_rightOut_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixed_leftIn_rightOut_and_truth_lift

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_from_star_maximalMixed_leftIn_rightOut_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_star_maximalMixed_leftIn_rightOut_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_star_maximalMixed_leftIn_rightOut_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)] :
    RM.HasCoreCountermodel σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    RM.HasCoreCountermodel σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)] :
    RM.HasCoreCountermodel σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)] :
    RMSeq.HasFromCoreSeqCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferNegImpLift σ]
    [RM.HasCanonicalStarTransferQuantifierLift σ] :
    RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ) :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthLift σ] :
    RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ) :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferNegImpLift σ]
    [RM.HasCanonicalStarTransferQuantifierLift σ] :
    RM.HasCoreCountermodel σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthLift σ] :
    RM.HasCoreCountermodel σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferNegImpLift σ]
    [RM.HasCanonicalStarTransferQuantifierLift σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthLift σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferNegImpLift σ]
    [RM.HasCanonicalStarTransferQuantifierLift σ] :
    RMSeq.HasFromCoreSeqCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    RM.HasCanonicalStarTransferNegImpLift σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    RM.HasCanonicalStarTransferQuantifierLift σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    RM.HasCanonicalStarTransferTruthLift σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    RM.HasCoreCountermodel σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    RMSeq.HasFromCoreSeqCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)] :
    RM.HasCanonicalStarTransferTruthBySize σ :=
  RM.canonicalStarTransfer_truthBySize_of_truthLift (σ := σ)

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferNegImpLift σ]
    [RM.HasCanonicalStarTransferQuantifierLift σ] :
    RM.HasCanonicalStarTransferTruthBySize σ :=
  RM.canonicalStarTransfer_truthBySize_of_split (σ := σ)

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthLift σ] :
    RM.HasCanonicalStarTransferTruthBySize σ :=
  RM.canonicalStarTransfer_truthBySize_of_truthLiftBundle (σ := σ)

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_canonicalStarTransferTruthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_canonicalStarTransferTruthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasCanonicalStarTransferTruthLift σ] :
    RMSeq.HasFromCoreSeqCompleteness σ :=
  inferInstance

example {σ : Type} [P : RM.HasPrimeTheoryTruthModelProp σ] [RM.HasPrimeTheoryTruthLift σ P] :
    RMSeq.HasFromCoreSeqCompleteness σ :=
  inferInstance

example {σ : Type} [P : RM.HasPrimeTheoryTruthModelProp σ] [RM.HasPrimeTheoryTruthLift σ P] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModel σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthObligationsProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCompleteProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ] :
    RM.CanonicalPair.HasPrimeReflectionLift σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ] :
    RM.CanonicalPair.HasPrimeTransferLift σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedTransferRealization σ] :
    RM.CanonicalPair.HasPrimeTransferLift σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ] :
    RM.CanonicalPair.HasMaximalMixedTransferRealization σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightPrimeRealization σ] :
    RM.CanonicalPair.HasMaximalMixedTransferRealization σ :=
  RM.CanonicalPair.hasMaximalMixedTransferRealization_of_split (σ := σ)

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedLeftPrimeRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightPrimeRealization σ] :
    RM.CanonicalPair.HasMaximalMixedTransferRealization σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ] :
    RM.CanonicalPair.HasMaximalMixedTransferRealization σ :=
  RM.CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [RM.CanonicalPair.HasMaximalMixedRightOutRealization σ] :
    RM.CanonicalPair.HasMaximalMixedTransferRealization σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedRightDerivabilityGap σ] :
    RM.CanonicalPair.HasMaximalMixedRightOutRealization σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedLeftPrimeRealization σ] :
    RM.CanonicalPair.HasMaximalMixedLeftDerivabilityGap σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasMaximalMixedRightPrimeRealization σ] :
    RM.CanonicalPair.HasMaximalMixedRightDerivabilityGap σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasPrimeTheoryAvoidSet σ]
    [RM.CanonicalPair.HasMaximalMixedLeftDerivabilityGap σ] :
    RM.CanonicalPair.HasMaximalMixedLeftInRealization σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ] :
    RM.HasCanonicalImpCounterexampleProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeLift σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasPrimeLift σ] :
    RM.HasCanonicalImpCounterexampleProp σ :=
  RM.CanonicalPair.hasCanonicalImpCounterexampleProp_of_seed_lift

example {σ : Type}
    [RM.CanonicalPair.HasPrimeTransferLift σ] :
    RM.CanonicalPair.HasPrimeLift σ :=
  inferInstance

example {σ : Type}
    [RM.CanonicalPair.HasPrimeReflectionLift σ] :
    RM.CanonicalPair.HasPrimeTransferLift σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalImpCounterexampleProp σ] :
    RM.CanonicalPair.HasPrimeLift σ :=
  RM.CanonicalPair.hasPrimeLift_of_counterexample

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ] :
    RM.CanonicalPair.HasPrimeLift σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ] :
    RM.CanonicalPair.HasPrimeTransferLift σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ] :
    RM.HasCanonicalStarExistsProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ] :
    RM.HasCanonicalPrimeRelProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ] :
    RM.HasPrimeTheoryTruthModelProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ] :
    RM.HasPrimeTheoryTruthModelProp σ :=
  RM.canonicalModelPropOfStarTransfer σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ] :
    RM.HasCanonicalPrimeRelProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeLift σ] :
    RM.HasCanonicalPrimeRelProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeReflectionLift σ] :
    RM.HasCanonicalPrimeRelProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarExistsProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ] :
    RMSeq.HasFromCoreSeqCompletenessProp σ :=
  inferInstance

example {σ : Type}
    [RM.HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_prime_truth_model hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_prime_truth_model_via_obligations hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_prime_truth_model_via_canonical_prime_rel hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_prime_truth_obligations hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_star_imp hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_star_counterexample hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) :=
  RM.rmseq_syn_completeness_prop_from_star_maximalMixedPrimeRealization hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_star_maximalMixedPrimeRealization hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_star_maximalMixedPrimeRealization_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarExistsProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_star_exists_counterexample hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_star_exists_counterexample hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) :=
  RM.rmseq_syn_completeness_prop_from_star_reflection_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_star_reflection_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) :=
  RM.rmseq_syn_completeness_prop_from_star_transfer_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) ↔ RM.Entails Γ φ :=
  RM.rmseq_syn_adequacy_prop_from_star_transfer_lift hΓ hφ

example {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.DerivesCore Γ φ → RM.Entails Γ φ :=
  RM.rm_core_soundness

example {σ : Type} [RM.HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_from_countermodel

example {σ : Type} [RM.HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_countermodel

example {σ : Type}
    [RM.HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_prime_truth_model

example {σ : Type}
    [RM.HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_from_prime_truth_model_via_obligations

example {σ : Type}
    [RM.HasPrimeTheoryTruthObligations σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_prime_truth_obligations

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryTruthLift σ P]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_prime_truth_lift

example {σ : Type}
    [RM.HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_from_prime_truth_model_via_lift_explicit

example {σ : Type}
    [RM.HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_model hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_model_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_model_via_obligations hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_model_via_canonical_prime_rel hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_obligations hΓ hφ

example {σ : Type}
    [RM.HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_prime_truth_obligations_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_canonical_prime_rel hΓ hφ

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_canonical_prime_rel_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_prop_from_canonical_prime_rel_via_star_seed_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_prop_from_canonical_prime_rel_via_star_seed_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → RMSeq.DerivesSyn (RMSeq.fromCore Γ φ) :=
  RM.rmseq_syn_completeness_prop_from_canonical_prime_rel_via_star_seed_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_imp hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_imp_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_counterexample hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_prop_from_star_maximalMixedPrimeRealization hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_prop_from_star_maximalMixedPrimeRealization hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_maximalMixedPrimeRealization hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_seed_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_prop_from_star_reflection_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_reflection_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  RM.rm_core_completeness_prop_from_star_transfer_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_transfer_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_seed_lift_of_counterexample hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_counterexample_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_maximalMixedPrimeRealization_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_seed_lift_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_reflection_lift_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_transfer_lift_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarExistsProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_exists_counterexample hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_exists_counterexample hΓ hφ

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_canonical_prime_rel_via_star_seed_lift hΓ hφ

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_canonical_prime_rel_via_star_seed_lift_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalStarExistsProp σ]
    [RM.HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_exists_counterexample_via_seqclass hΓ hφ

example {σ : Type}
    [RM.HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_prop_from_star_exists_counterexample hΓ hφ

example {σ : Type} [RM.HasCoreCountermodel σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  RM.hasCoreCompleteness_from_countermodel σ

example {σ : Type} :
    NDRMSyntax.HasCoreCompleteness σ :=
  inferInstance

example {σ : Type} [RM.HasPrimeTheoryTruthModel σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  RM.hasCoreCompleteness_from_prime_theory_truth σ

example {σ : Type}
    [P : RM.HasPrimeTheoryTruthModelProp σ]
    [RM.HasPrimeTheoryTruthLift σ P] :
    NDRMSyntax.HasCoreCompleteness σ :=
  RM.hasCoreCompleteness_from_modelProp_lift σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasPrimeTransferLift σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ :=
  RM.hasCoreCompleteness_from_star_transfer_lift_and_truth_lift σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)] :
    RM.HasCoreCountermodel σ :=
  RM.hasCoreCountermodel_from_star_maximalMixedPrimeRealization_and_truth_lift σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasPrimeTheoryTruthLift σ (RM.canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ :=
  RM.hasCoreCompleteness_from_star_maximalMixedPrimeRealization_and_truth_lift σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    RM.HasCoreCountermodel σ :=
  RM.hasCoreCountermodel_from_star_maximalMixedPrimeRealization_and_truthBySize σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  RM.hasCoreCompleteness_from_star_maximalMixedPrimeRealization_and_truthBySize σ

example {σ : Type} [RM.HasHenkinCoreCountermodel σ] :
    RM.HasCoreCountermodel σ :=
  inferInstance

example {σ : Type} :
    RM.HasHenkinCoreCountermodel σ :=
  inferInstance

example {σ : Type} [RM.HasCoreCountermodel σ] :
    RM.HasHenkinCoreCountermodel σ :=
  RM.hasHenkinCoreCountermodel_of_coreCountermodel σ

example {σ : Type} [RM.HasHenkinCoreCountermodel σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  RM.hasCoreCompleteness_of_henkinCoreCountermodel σ

example {σ : Type}
    [RM.HasHenkinCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_henkin_from_henkinCountermodel

example {σ : Type}
    [RM.HasHenkinCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_henkin_from_henkinCountermodel

example {σ : Type}
    [RM.HasHenkinCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_henkin_from_henkinCountermodel_via_seqclass

example {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_henkin_closed

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasStarMaximalMixedHenkinTruthBySize σ] :
    RM.HasHenkinCoreCountermodel σ :=
  RM.hasHenkinCoreCountermodel_from_star_maximalMixed_henkinTruthBySize σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasStarMaximalMixedHenkinTruthBySize σ] :
    RM.HasHenkinCoreCountermodel σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasStarMaximalMixedHenkinTruthBySize σ] :
    RM.HasCoreCountermodel σ :=
  RM.hasCoreCountermodel_from_star_maximalMixed_henkinTruthBySize σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasStarMaximalMixedHenkinTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  RM.hasCoreCompleteness_from_star_maximalMixed_henkinTruthBySize σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasStarMaximalMixedHenkinTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasStarMaximalMixedHenkinTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_henkin_from_star_maximalMixed_henkinTruthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasStarMaximalMixedHenkinTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_henkin_from_star_maximalMixed_henkinTruthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasStarMaximalMixedHenkinTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_henkin_from_star_maximalMixed_henkinTruthBySize_via_seqclass

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    RM.HasStarMaximalMixedHenkinTruthBySize σ :=
  inferInstance

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ] :
    RM.HasHenkinCoreCountermodel σ :=
  RM.hasHenkinCoreCountermodel_from_star_maximalMixedPrimeRealization_and_truthBySize σ

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  RM.rm_completeness_henkin_from_star_maximalMixedPrimeRealization_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_henkin_from_star_maximalMixedPrimeRealization_and_truthBySize

example {σ : Type}
    [RM.HasCanonicalStarProp σ]
    [RM.CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [RM.HasCanonicalStarTransferTruthBySize σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_henkin_from_star_maximalMixed_henkinTruthBySize

end Tests
end Noneism
end HeytingLean
