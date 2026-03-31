import HeytingLean.InqBQ

namespace HeytingLean.Tests.InqBQ

open HeytingLean.InqBQ

#check Signature
#check Term
#check Formula
#check InfoModel
#check Assignment
#check Assignment.update
#check denote
#check supports
#check supports_mono
#check supports_empty
#check holdsAt
#check globallySupports
#check entails
#check valid
#check equiv
#check idEntails
#check rhoRigidEq
#check Formula.isClassical
#check Formula.dependence
#check worldSatisfies
#check truthConditional
#check classicallyEntails
#check classical_truth
#check classical_conservativity
#check SigmaAB
#check H10UPC
#check h10upcSemDirect
#check H10UPCSat
#check listWitness
#check h10upcSat_iff_exists_listWitness
#check h10upcSat_re
#check h10upcSat_compl_not_re_of_not_computable
#check finNum
#check finNum_fin
#check Model
#check model_fin
#check m_listable
#check modelRel
#check modelRelVec2
#check m_decidable
#check associatedRelation
#check isFull
#check canonicalFull
#check eta
#check theta
#check chiN
#check GammaNC
#check eta_captures_finiteness
#check theta_captures_nonfullness
#check models_chiN_iff_card_ge
#check gammaNC_idEntails_theta
#check gammaNC_entails_rhoRigidEq_imp_theta
#check inqbq_not_compact_id
#check inqbq_not_compact
#check ABSignature
#check ClassicalStructure
#check generalizedCanonicalFullIdModel
#check classical_support_in_canonical
#check finiteFOLValid
#check finite_validity_reduction
#check ReductionSig
#check h10upcFiniteValidityFormula_correct_forward
#check h10upcFiniteValidityFormula_complete
#check Imported.h10upcFiniteValidityFormula_correct
#check finiteValidityFamily
#check reductionValidityFormula
#check reductionValidityFormula_correct
#check PointwiseHardnessBridge
#check notRE_of_pointwise_iff
#check h10upcToFiniteValidityBridge
#check finite_validity_family_not_re
#check inqbq_validity_family_not_re
#check HardnessRegistryMeta
#check HardnessRegistryEntry
#check hardnessRegistry
#check hardnessRegistryMeta
#check findEntryByBenchmarkId?
#check findMetaByBenchmarkId?
#check REPred.of_manyOneReducible
#check not_computable_of_manyOneReducible
#check not_re_of_not_computable_of_re_compl
#check not_re_of_manyOneReducible
#check CoqReflects
#check CoqDecidable
#check CoqRecEnum
#check coqDecidable_of_decidablePred
#check coqRecEnum_of_rePred
#check CoqComplement
#check CoqEnumerator
#check CoqEnumerable
#check CoqReduction
#check CoqReduces
#check CoqUndecidable
#check coqReduces_complement
#check coqUndecidable_of_reduces
#check coqDecidable_of_computablePred
#check not_computable_of_coqUndecidable
#check not_re_of_coqUndecidable_complement
#check imported_h10upcSat_compl_not_computable
#check imported_h10upcSat_compl_not_re
#check InfoProp
#check InfoProp.supportProp
#check truthClosure
#check truthClosure_is_nucleus
#check truthClosure_supportProp_eq_of_classical
#check Team
#check inducedTeam
#check teamDepends
#check dep_team_equiv

example : globallySupports (canonicalFull (Fin 3)) (fun _ => ⟨0, by decide⟩) eta := by
  exact
    (eta_captures_finiteness
      (M := canonicalFull (Fin 3))
      (canonicalFull_isFull (Fin 3))
      (canonicalFull_isIdModel (Fin 3))
      (fun _ => ⟨0, by decide⟩)).2 (show Finite (Fin 3) from inferInstance)

example : ¬ globallySupports (canonicalFull ℕ) (fun _ => (0 : ℕ)) eta := by
  intro h
  have hFin : Finite ℕ :=
    (eta_captures_finiteness
      (M := canonicalFull ℕ)
      (canonicalFull_isFull ℕ)
      (canonicalFull_isIdModel ℕ)
      (fun _ => (0 : ℕ))).1 h
  exact hFin.false

example :
    globallySupports (canonicalFull (Fin 4)) (fun _ => ⟨0, by decide⟩) (chiN 3) := by
  exact canonicalFull_supports_chiN 3 3 (fun _ => ⟨0, by decide⟩) (by decide)

example :
    ¬ globallySupports (canonicalFull (Fin 2)) (fun _ => ⟨0, by decide⟩) theta := by
  exact canonicalFull_not_theta 1 (fun _ => ⟨0, by decide⟩)

example : listable (Model 2) := by
  exact m_listable 2

example : modelRel 3 (.num ⟨1, by decide⟩) (.num ⟨2, by decide⟩) := by
  decide

example :
    ¬ REPred finiteValidityFamily := by
  exact finite_validity_family_not_re

end HeytingLean.Tests.InqBQ
