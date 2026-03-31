import HeytingLean.Hyperseries.SurrealDescription
import HeytingLean.Hyperseries.SurrealExpLogSemantics
import HeytingLean.Hyperseries.Eval
import HeytingLean.Hyperseries.CompletionGate
import HeytingLean.Hyperseries.Category.CanonicalizationBridge

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries

noncomputable section

example (a : Surreal) :
    HyperserialDescription.realize (K := Surreal)
      (HyperserialDescription.describe (K := Surreal) a) = a := by
  exact HyperserialDescription.realize_describe (K := Surreal) a

example (x : Surreal) :
    (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).exp x = x := by
  simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]

example (x : Surreal) :
    (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).log x = x := by
  simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]

example :
    ¬SurrealExpLogSemantics.Nontrivial SurrealExpLogSemantics.active := by
  exact SurrealExpLogSemantics.not_nontrivial_active

example :
    SurrealExpLogSemantics.active = SurrealExpLogSemantics.default := by
  exact SurrealExpLogSemantics.active_eq_default

example :
    SurrealExpLogSemantics.activeUseNontrivial = false := by
  simp

example :
    SurrealExpLogSemantics.active = SurrealExpLogSemantics.select false := by
  exact SurrealExpLogSemantics.active_eq_select_false

example :
    ¬SurrealExpLogSemantics.Nontrivial SurrealExpLogSemantics.active := by
  exact SurrealExpLogSemantics.not_nontrivial_active

example :
    SurrealExpLogSemantics.active ≠ SurrealExpLogSemantics.select true := by
  exact SurrealExpLogSemantics.active_ne_select_true

example :
    surrealSemanticsDefault = SurrealExpLogSemantics.active := by
  exact surrealSemanticsDefault_eq_active

example :
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active := by
  exact surrealModel_eq_activeModel

example :
    surrealModel = surrealModelWith false := by
  exact surrealModel_eq_modelWith_false

example :
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default := by
  exact surrealModel_eq_defaultModel

example :
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder := by
  exact surrealModel_eq_placeholderModel

example (b : Bool) :
    surrealModelWith b = SurrealExpLogSemantics.toModel (surrealSemantics b) := by
  exact surrealModelWith_eq_toModel b

example :
    surrealSemantics true = SurrealExpLogSemantics.negSemantics := by
  exact surrealSemantics_true

example :
    SurrealExpLogSemantics.Nontrivial (surrealSemantics true) := by
  simpa [surrealSemantics] using SurrealExpLogSemantics.nontrivial_select_true

example :
    surrealModelWith false = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default := by
  exact surrealModelWith_false

example :
    surrealModelWith true = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.negSemantics := by
  exact surrealModelWith_true

example (x : Surreal) :
    (surrealModelWith false).exp x = x := by
  simp [surrealModelWith, surrealSemantics]

example (x : Surreal) :
    (surrealModelWith false).log x = x := by
  simp [surrealModelWith, surrealSemantics]

example (α : Ordinal) (x : Surreal) :
    (surrealModelWith false).hyperExp α x = x := by
  simp [surrealModelWith, surrealSemantics]

example (α : Ordinal) (x : Surreal) :
    (surrealModelWith false).hyperLog α x = x := by
  simp [surrealModelWith, surrealSemantics]

example (b : Bool) :
    (surrealModelWith b).omega = omegaSurreal := by
  simp [surrealModelWith, surrealSemantics]

example (b : Bool) (x : Surreal) :
    (surrealModelWith b).exp x = (if b then -x else x) := by
  simp [surrealModelWith, surrealSemantics]

example (b : Bool) (x : Surreal) :
    (surrealModelWith b).log x = (if b then -x else x) := by
  simp [surrealModelWith, surrealSemantics]

example (b : Bool) (x : Surreal) :
    (surrealModelWith b).hyperExp 0 x = (if b then -x else x) := by
  simp [surrealModelWith, surrealSemantics]

example (b : Bool) (x : Surreal) :
    (surrealModelWith b).hyperLog 0 x = (if b then -x else x) := by
  simp [surrealModelWith, surrealSemantics]

example (x : Surreal) :
    (surrealModelWith true).exp x = -x := by
  simp [surrealModelWith, surrealSemantics]

example (x : Surreal) :
    (surrealModelWith true).log x = -x := by
  simp [surrealModelWith, surrealSemantics]

example (x : Surreal) :
    (surrealModelWith true).hyperExp 0 x = -x := by
  simp [surrealModelWith, surrealSemantics]

example (x : Surreal) :
    (surrealModelWith true).hyperLog 0 x = -x := by
  simp [surrealModelWith, surrealSemantics]

example (α : Ordinal) (x : Surreal) :
    (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).hyperExp α x = x := by
  simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]

example (α : Ordinal) (x : Surreal) :
    (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).hyperLog α x = x := by
  simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]

example (α : Ordinal) (x : Surreal) :
    surrealModel.hyperExp α x = x := by
  simp [surrealModel]

example (α : Ordinal) (x : Surreal) :
    surrealModel.hyperLog α x = x := by
  simp [surrealModel]

example (x : Surreal) :
    surrealModel.exp x = x := by
  simp [surrealModel]

example (x : Surreal) :
    surrealModel.log x = x := by
  simp [surrealModel]

example (e : HExpr) :
    HExpr.eval surrealModel e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e := by
  exact HExpr.eval_surrealModel_eq_activeModel e

example (e : HExpr) :
    HExpr.eval surrealModel e = HExpr.eval (surrealModelWith false) e := by
  exact HExpr.eval_surrealModel_eq_modelWith_false e

example (e : HExpr) :
    HExpr.eval surrealModel e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e := by
  exact HExpr.eval_surrealModel_eq_defaultModel e

example (e : HExpr) :
    HExpr.eval surrealModel e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
  exact HExpr.eval_surrealModel_eq_placeholderModel e

example (e : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
  exact HExpr.eval_defaultModel_eq_placeholderModel e

example (e : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e := by
  exact HExpr.eval_activeModel_eq_defaultModel e

example (e : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
  exact HExpr.eval_activeModel_eq_placeholderModel e

example {K : Type*} [CommRing K] {M N : HyperserialModel K} (h : M = N) (e : HExpr) :
    HExpr.eval M e = HExpr.eval N e := by
  exact HExpr.eval_eq_of_model_eq h e

example {K : Type*} [Field K] {M N : HyperserialModel K} (h : M = N) (e : HExprQ) :
    HExprQ.eval M e = HExprQ.eval N e := by
  exact HExprQ.eval_eq_of_model_eq h e

example :
    (∀ x : Surreal, (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).exp x = x) ∧
      (∀ x : Surreal, (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).log x = x) ∧
      ¬SurrealExpLogSemantics.Nontrivial SurrealExpLogSemantics.active := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]
  · intro x
    simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]
  · exact SurrealExpLogSemantics.not_nontrivial_active

example :
    SurrealExpLogSemantics.Nontrivial (SurrealExpLogSemantics.select true) := by
  simpa using SurrealExpLogSemantics.nontrivial_select_true

example :
    ¬SurrealExpLogSemantics.Nontrivial (SurrealExpLogSemantics.select false) := by
  simpa using SurrealExpLogSemantics.not_nontrivial_select_false

example (x : Surreal) :
    (SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)).exp x = -x := by
  simp [SurrealExpLogSemantics.toModel, SurrealExpLogSemantics.select]

example :
    SurrealExpLogSemantics.Nontrivial (SurrealExpLogSemantics.select true) ∧
      ¬SurrealExpLogSemantics.Nontrivial (SurrealExpLogSemantics.select false) := by
  exact ⟨SurrealExpLogSemantics.nontrivial_select_true,
    SurrealExpLogSemantics.not_nontrivial_select_false⟩

example (a : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) a := by
  exact HeytingLean.Hyperseries.Category.eval_eq_of_rewrite_steps
    (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
    (h := HeytingLean.Hyperseries.Category.HRewriteSteps.single
      (HeytingLean.Hyperseries.Category.HRewrite1.add_zero_right a))

example (a : HExpr) :
    HeytingLean.Hyperseries.Category.NormalizedConnected
      (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (ExprC.add a (ExprC.C (0 : ℤ))) a := by
  exact HeytingLean.Hyperseries.Category.rewrite_steps_implies_normalizedConnected
    (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (h := HeytingLean.Hyperseries.Category.HRewriteSteps.single
      (HeytingLean.Hyperseries.Category.HRewrite1.add_zero_right a))

example (a : HExpr) :
    HExpr.eval surrealModel (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval surrealModel a := by
  exact HeytingLean.Hyperseries.Category.eval_eq_of_rewrite_steps
    (M := surrealModel)
    (h := HeytingLean.Hyperseries.Category.HRewriteSteps.single
      (HeytingLean.Hyperseries.Category.HRewrite1.add_zero_right a))

example (a : HExpr) :
    HeytingLean.Hyperseries.Category.NormalizedConnected
      (M := surrealModel)
      (ExprC.add a (ExprC.C (0 : ℤ))) a := by
  exact HeytingLean.Hyperseries.Category.rewrite_steps_implies_normalizedConnected
    (M := surrealModel)
    (h := HeytingLean.Hyperseries.Category.HRewriteSteps.single
      (HeytingLean.Hyperseries.Category.HRewrite1.add_zero_right a))

section NameWiringSmoke

#check SurrealDescCode
#check instHyperserialDescriptionSurreal
#check SurrealExpLogSemantics.default
#check SurrealExpLogSemantics.activeUseNontrivial
#check SurrealExpLogSemantics.active
#check SurrealExpLogSemantics.placeholder
#check SurrealExpLogSemantics.select
#check SurrealExpLogSemantics.nontrivial_select_true
#check SurrealExpLogSemantics.nontrivial_select_iff
#check SurrealExpLogSemantics.not_nontrivial_select_iff
#check SurrealExpLogSemantics.active_eq_select_false
#check SurrealExpLogSemantics.not_nontrivial_active
#check SurrealExpLogSemantics.active_ne_select_true
#check surrealSemanticsDefault_eq_active
#check surrealSemantics_true
#check surrealModelWith_eq_toModel
#check surrealModelWith_false
#check surrealModelWith_true
#check surrealModelWith_false_exp
#check surrealModelWith_false_log
#check surrealModelWith_false_hyperExp
#check surrealModelWith_false_hyperLog
#check surrealModel_eq_activeModel
#check surrealModel_eq_modelWith_false
#check surrealModel_eq_defaultModel
#check surrealModel_eq_placeholderModel
#check surrealModel_omega
#check surrealModelWith_omega
#check surrealModelWith_exp_if
#check surrealModelWith_log_if
#check surrealModelWith_hyperExp_zero_if
#check surrealModelWith_hyperLog_zero_if
#check HExpr.eval_surrealModel_eq_modelWith_false
#check HExpr.eval_surrealModel_eq_activeModel
#check HExpr.eval_surrealModel_eq_defaultModel
#check HExpr.eval_surrealModel_eq_placeholderModel
#check HExpr.eval_defaultModel_eq_placeholderModel
#check HExpr.eval_activeModel_eq_defaultModel
#check HExpr.eval_activeModel_eq_placeholderModel
#check HExpr.eval_eq_of_model_eq
#check HExprQ.eval_eq_of_model_eq
#check gate_eval_eq_of_groupoid_hom_generic
#check gate_eval_eq_of_connected_generic
#check gate_eval_eq_of_rewrite_steps_generic
#check gate_eval_eq_of_rewrite1_generic
#check gate_connected_of_rewrite1_generic
#check gate_eval_eq_of_quiver_hom_generic
#check gate_canonicalDesc_eq_of_groupoid_hom_generic
#check gate_canonicalDesc_eq_of_connected_generic
#check gate_normalizedConnected_refl_generic
#check gate_normalizedConnected_symm_generic
#check gate_normalizedConnected_trans_generic
#check gate_NormalizedQuotient_generic
#check gate_quotient_eq_of_normalizedConnected_generic
#check gate_normalizedConnected_of_quotient_eq_generic
#check gate_canonicalDescClass_eq_of_normalizedConnected_generic
#check gate_rewrite_steps_implies_normalizedConnected_generic
#check gate_groupoid_hom_implies_canonicalDesc_eq_generic
#check gate_connected_implies_canonicalDesc_eq_generic
#check gate_fiber_refl_generic
#check gate_fiber_connected_generic
#check gate_fiber_to_center_generic
#check gate_center_to_fiber_generic
#check gate_eval_eq_of_fiber_generic
#check gate_normalizedConnected_of_fiber_generic
#check gate_canonicalDesc_eq_of_fiber_generic
#check gate_quotient_eq_of_fiber_generic
#check gate_canonicalDescClass_eq_of_fiber_generic
#check gate_normalizedConnected_of_uniqueNF_generic
#check gate_quotient_eq_of_uniqueNF_generic
#check gate_canonicalDesc_eq_of_uniqueNF_generic
#check gate_canonicalDesc_nf_eq_of_uniqueNF_generic
#check gate_canonicalDescClass_eq_of_uniqueNF_generic
#check gate_canonicalDescClass_mk_eq_of_uniqueNF_generic
#check gate_normalizedConnected_of_rewrite_steps_generic
#check gate_canonicalDesc_eq_iff_normalizedConnected_generic
#check gate_quotient_eq_iff_normalizedConnected_generic
#check gate_quotient_eq_iff_canonicalDescClass_mk_eq_generic
#check gate_canonicalDescClass_mk_eq_iff_normalizedConnected_generic
#check gate_normalizedConnected_of_canonicalDescClass_mk_eq_generic
#check gate_quotient_eq_of_canonicalDescClass_mk_eq_generic
#check gate_canonicalDescClass_mk_eq_of_quotient_eq_generic
#check gate_canonicalDescClass_mk_eq_of_rewrite_steps_generic
#check gate_canonicalDescClass_mk_eq_of_groupoid_hom_generic
#check gate_canonicalDescClass_mk_eq_of_connected_generic
#check gate_quotient_eq_of_rewrite_steps_generic
#check gate_quotient_eq_of_canonicalDesc_eq_generic
#check gate_canonicalDesc_eq_of_quotient_eq_generic
#check gate_canonicalDesc_eq_iff_quotient_eq_generic
#check gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_generic
#check gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_generic
#check gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_generic
#check gate_rewriteComplete_of_valuation_bridge_generic
#check gate_eval_eq_of_canonicalDesc_eq_generic
#check gate_connected_of_canonicalDesc_eq_generic
#check gate_canonicalDesc_eq_iff_connected_generic
#check gate_canonicalFiber_connected_generic
#check gate_canonicalFiber_contractible_at_generic
#check gate_canonicalFiber_connected_of_valuation_generic
#check gate_canonicalFiber_contractible_at_of_valuation_generic
#check gate_canonicalDesc_eq_of_canonicalValuationFiber_generic
#check gate_valuation_eq_of_canonicalValuationFiber_generic
#check gate_eval_eq_of_canonicalValuationFiber_generic
#check gate_canonicalValuationFiber_connected_generic
#check gate_canonicalValuationFiber_contractible_at_generic
#check gate_normalizedConnected_of_canonicalValuationFiber_generic
#check gate_quotient_eq_of_canonicalValuationFiber_generic
#check gate_canonicalDescClass_eq_of_canonicalValuationFiber_generic
#check gate_normalizedConnected_implies_connected_nf_generic
#check gate_normalizedConnected_iff_connected_nf_generic
#check gate_canonicalDesc_nf_eq_iff_connected_nf_generic
#check gate_connected_nf_of_canonicalDesc_nf_eq_generic
#check gate_canonicalDesc_nf_eq_of_connected_nf_generic
#check gate_connected_of_shared_fiber_generic
#check gate_connected_nf_of_shared_fiber_generic
#check gate_canonicalDesc_eq_of_shared_fiber_generic
#check gate_canonicalDesc_eq_nf_of_shared_fiber_generic
#check gate_quotient_eq_of_shared_fiber_generic
#check gate_canonicalDescClass_mk_eq_of_shared_fiber_generic
#check gate_connected_of_canonicalDesc_eq_of_rewriteComplete_generic
#check gate_canonicalDesc_eq_iff_connected_of_rewriteComplete_generic
#check gate_canonicalDesc_eq_of_connected_of_rewriteComplete_generic
#check gate_quotient_eq_iff_connected_of_rewriteComplete_generic
#check gate_canonicalDesc_eq_iff_quotient_eq_of_rewriteComplete_generic
#check gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_rewriteComplete_generic
#check gate_canonicalDescClass_mk_eq_iff_connected_nf_generic
#check gate_canonicalDescClass_mk_eq_iff_normalizedConnected_of_rewriteComplete_generic
#check gate_normalizedConnected_of_canonicalDescClass_mk_eq_of_rewriteComplete_generic
#check gate_canonicalDescClass_mk_eq_of_normalizedConnected_of_rewriteComplete_generic
#check gate_canonicalDescClass_mk_eq_iff_connected_generic
#check gate_connected_nf_of_canonicalDescClass_mk_eq_generic
#check gate_connected_of_canonicalDescClass_mk_eq_generic
#check gate_canonicalDescClass_mk_eq_of_connected_nf_generic
#check gate_quotient_eq_of_connected_generic
#check gate_connected_of_quotient_eq_generic
#check gate_quotient_eq_iff_connected_generic
#check gate_canonicalDescClass_mk_eq_iff_quotient_eq_generic
#check gate_canonicalDesc_eq_of_quotient_eq_of_rewriteComplete_generic
#check gate_quotient_eq_of_canonicalDesc_eq_of_rewriteComplete_generic
#check gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_rewriteComplete_generic
#check gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_rewriteComplete_generic
#check gate_canonicalDescClass_mk_eq_iff_normalizedConnected_of_valuation_generic
#check gate_normalizedConnected_of_canonicalDescClass_mk_eq_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_of_normalizedConnected_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_iff_connected_of_valuation_generic
#check gate_connected_of_canonicalDescClass_mk_eq_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_of_connected_of_valuation_generic
#check gate_quotient_eq_of_connected_of_valuation_generic
#check gate_connected_of_quotient_eq_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_generic
#check gate_quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_generic
#check gate_canonicalDesc_eq_of_quotient_eq_of_valuation_generic
#check gate_quotient_eq_of_canonicalDesc_eq_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_generic
#check gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_generic
#check gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_index_generic
#check gate_canonicalDescClass_mk_eq_iff_connected_of_valuation_index_generic
#check gate_connected_of_canonicalDescClass_mk_eq_of_valuation_index_generic
#check gate_canonicalDescClass_mk_eq_of_connected_of_valuation_index_generic
#check gate_quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_index_generic
#check gate_canonicalDesc_eq_iff_connected_class_quotient_of_valuation_index_generic
#check gate_canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_index_generic
#check gate_quotient_eq_iff_connected_class_of_valuation_index_generic
#check gate_canonicalDesc_eq_iff_connected_of_valuation_generic
#check gate_connected_of_canonicalDesc_eq_of_valuation_generic
#check gate_canonicalDesc_eq_of_connected_of_valuation_generic
#check gate_quotient_eq_iff_connected_of_valuation_generic
#check gate_canonicalDesc_eq_iff_quotient_eq_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_generic
#check gate_canonicalDesc_eq_iff_connected_class_quotient_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_generic
#check gate_quotient_eq_iff_connected_class_of_valuation_generic
#check gate_canonicalDesc_class_quotient_connected_bundle_of_valuation_generic
#check gate_connected_class_quotient_of_canonicalDesc_eq_of_valuation_generic
#check gate_canonicalDesc_eq_of_connected_class_quotient_of_valuation_generic
#check gate_connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_generic
#check gate_connected_class_of_quotient_eq_of_valuation_generic
#check gate_quotient_eq_of_connected_class_of_valuation_generic
#check gate_canonicalDesc_eq_iff_connected_of_valuation_index_generic
#check gate_connected_of_canonicalDesc_eq_of_valuation_index_generic
#check gate_canonicalDesc_eq_of_connected_of_valuation_index_generic
#check gate_quotient_eq_of_canonicalDesc_eq_of_valuation_index_generic
#check gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_index_generic
#check gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_index_generic
#check gate_quotient_eq_iff_connected_of_valuation_index_generic
#check gate_connected_of_quotient_eq_of_valuation_index_generic
#check gate_quotient_eq_of_connected_of_valuation_index_generic
#check gate_canonicalDesc_eq_iff_quotient_eq_of_valuation_index_generic
#check gate_canonicalDesc_eq_of_quotient_eq_of_valuation_index_generic
#check gate_canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_index_generic
#check gate_canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_index_generic
#check gate_canonicalDesc_class_quotient_connected_bundle_of_valuation_index_generic
#check gate_connected_class_quotient_of_canonicalDesc_eq_of_valuation_index_generic
#check gate_canonicalDesc_eq_of_connected_class_quotient_of_valuation_index_generic
#check gate_connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_index_generic
#check gate_canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_index_generic
#check gate_connected_class_of_quotient_eq_of_valuation_index_generic
#check gate_quotient_eq_of_connected_class_of_valuation_index_generic
#check gate_canonicalDesc_class_quotient_connected_bundle_of_valuation_sameIndex_generic
#check gate_connected_class_quotient_of_canonicalDesc_eq_of_valuation_sameIndex_generic
#check gate_canonicalDesc_eq_of_connected_class_quotient_of_valuation_sameIndex_generic
#check gate_connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_sameIndex_generic
#check gate_canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_sameIndex_generic
#check gate_connected_class_of_quotient_eq_of_valuation_sameIndex_generic
#check gate_quotient_eq_of_connected_class_of_valuation_sameIndex_generic
#check gate_canonicalDesc_eq_iff_connected_class_quotient_of_valuation_sameIndex_generic
#check gate_canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_sameIndex_generic
#check gate_quotient_eq_iff_connected_class_of_valuation_sameIndex_generic
#check gate_connected_of_canonicalDesc_eq_of_valuation_sameIndex_core_generic
#check gate_quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core_generic
#check gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core_generic
#check gate_canonicalDesc_eq_iff_connected_of_valuation_sameIndex_generic
#check gate_connected_of_canonicalDesc_eq_of_valuation_sameIndex_generic
#check gate_canonicalDesc_eq_of_connected_of_valuation_sameIndex_generic
#check gate_canonicalDescClass_mk_eq_iff_connected_of_valuation_sameIndex_generic
#check gate_connected_of_canonicalDescClass_mk_eq_of_valuation_sameIndex_generic
#check gate_canonicalDescClass_mk_eq_of_connected_of_valuation_sameIndex_generic
#check gate_quotient_eq_iff_connected_of_valuation_sameIndex_generic
#check gate_connected_of_quotient_eq_of_valuation_sameIndex_generic
#check gate_quotient_eq_of_connected_of_valuation_sameIndex_generic
#check gate_canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_sameIndex_generic
#check gate_quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex_generic
#check gate_canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_sameIndex_generic
#check gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_sameIndex_generic
#check gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex_generic
#check gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex_generic
#check gate_canonicalDesc_eq_iff_quotient_eq_of_valuation_sameIndex_generic
#check gate_canonicalDesc_eq_of_quotient_eq_of_valuation_sameIndex_generic
#check gate_quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex_generic
#check gate_canonicalDesc_nf_eq_iff_connected_nf_of_valuation_generic
#check gate_normalizedConnected_iff_connected_nf_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_iff_connected_nf_of_valuation_generic
#check gate_connected_nf_of_canonicalDescClass_mk_eq_of_valuation_generic
#check gate_canonicalDescClass_mk_eq_of_connected_nf_of_valuation_generic
#check gate_connected_nf_of_canonicalDesc_nf_eq_of_valuation_generic
#check gate_canonicalDesc_nf_eq_of_connected_nf_of_valuation_generic
#check gate_active_canonicalDesc_eq_of_connected
#check gate_selectTrue_canonicalDesc_eq_of_connected
#check gate_modelWithTrue_canonicalDesc_eq_of_connected
#check gate_rewrite_eval_add_zero_generic
#check gate_rewrite_normalizedConnected_add_zero_generic
#check gate_realize_describe
#check gate_active_selector_false
#check gate_active_eq_placeholder
#check gate_active_eq_default
#check gate_active_eq_select_false
#check gate_active_not_nontrivial
#check gate_active_ne_select_true
#check gate_eval_default_semantics_eq_active
#check gate_eval_model_eq_active
#check gate_eval_model_eq_false
#check gate_eval_model_eq_default
#check gate_eval_model_eq_placeholder
#check gate_eval_model_with_eq_toModel
#check gate_eval_semantics_true_eq_neg
#check gate_eval_semantics_true_nontrivial
#check gate_eval_model_false_eq_default
#check gate_eval_model_false_exp
#check gate_eval_model_false_log
#check gate_eval_model_false_hyperExp
#check gate_eval_model_false_hyperLog
#check gate_eval_model_true_eq_neg
#check gate_eval_model_true_eq_select_true
#check gate_eval_model_true_omega
#check gate_eval_model_true_exp
#check gate_eval_model_true_log
#check gate_eval_model_true_hyperExp_zero
#check gate_eval_model_true_hyperLog_zero
#check gate_eval_model_exp_if
#check gate_eval_model_log_if
#check gate_eval_model_hyperExp_zero_if
#check gate_eval_model_hyperLog_zero_if
#check gate_eval_surrealModelWith_true_eq_select_true
#check gate_canonicalDesc_surrealModelWith_true_eq_select_true
#check gate_canonicalDescClass_mk_surrealModelWith_true_eq_select_true
#check gate_surrealModel_exp
#check gate_surrealModel_log
#check gate_surrealModel_hyperExp
#check gate_surrealModel_hyperLog
#check gate_eval_surrealModel_eq_active
#check gate_eval_surrealModel_eq_false
#check gate_eval_surrealModel_eq_default
#check gate_eval_surrealModel_eq_placeholder
#check gate_eval_default_eq_placeholder
#check gate_eval_active_eq_default
#check gate_eval_active_eq_placeholder
#check gate_eval_eq_of_model_eq
#check gate_evalQ_eq_of_model_eq
#check gate_placeholder_exp
#check gate_placeholder_log
#check gate_placeholder_hyperExp
#check gate_placeholder_hyperLog
#check gate_placeholder_not_nontrivial
#check gate_select_true_nontrivial
#check gate_select_false
#check gate_select_true
#check gate_nontrivial_select_iff
#check gate_not_nontrivial_select_iff
#check gate_nontrivial_active_iff
#check gate_not_nontrivial_active_iff
#check gate_toModel_select_false_exp
#check gate_toModel_select_false_log
#check gate_toModel_select_false_hyperExp
#check gate_toModel_select_false_hyperLog
#check gate_toModel_select_true_exp
#check gate_toModel_select_true_log
#check gate_toModel_select_true_hyperExp_zero
#check gate_toModel_select_true_hyperLog_zero
#check gate_toModel_select_true_hyperExp_succ
#check gate_toModel_select_true_hyperLog_succ
#check gate_not_nontrivial_identity
#check gate_toCore_identity
#check gate_HExpr1Obj_ofExpr
#check gate_HExpr1Obj_expr_ofExpr
#check gate_ofExpr
#check gate_expr_ofExpr
#check gate_HRewriteSteps
#check gate_hrewrite_steps_refl
#check gate_hrewrite_steps_single
#check gate_hrewrite_steps_trans
#check gate_hrewrite1_eval_sound
#check gate_hrewrite_steps_eval_sound
#check gate_refl
#check gate_single
#check gate_trans
#check gate_eval_sound
#check gate_quiver_hom_eval_sound
#check gate_HExprFreeGroupoid
#check gate_GObj
#check gate_hrewrite1_toGroupoid
#check gate_hrewrite1_toGroupoid_eval_sound
#check gate_hrewriteSteps_toGroupoid
#check gate_hrewriteSteps_toGroupoid_eval_sound
#check gate_toGroupoid
#check gate_toGroupoid_eval_sound
#check gate_HCatPkg
#check gate_HCat
#check gate_HCat_src
#check gate_HCat_tgt
#check gate_HCat_edge
#check gate_src
#check gate_tgt
#check gate_edge
#check gate_HDropLeft
#check gate_HDropRight
#check gate_HLeftTower
#check gate_HRightTower
#check gate_HOmegaLeft
#check gate_HOmegaRight
#check gate_HLeftTowerCone
#check gate_HRightTowerCone
#check gate_liftLeft
#check gate_liftRight
#check gate_liftLeft_fac
#check gate_liftRight_fac
#check gate_liftLeft_uniq
#check gate_liftRight_uniq
#check gate_eqToHom_app_left
#check gate_eqToHom_app_right
#check gate_HGCatPkg
#check gate_HGCat
#check gate_HGDropLeft
#check gate_HGDropRight
#check gate_HGLeftTower
#check gate_HGRightTower
#check gate_HGOmegaLeft
#check gate_HGOmegaRight
#check gate_HGLeftTowerCone
#check gate_HGRightTowerCone
#check gate_liftGLeft
#check gate_liftGRight
#check gate_liftGLeft_fac
#check gate_liftGRight_fac
#check gate_liftGLeft_uniq
#check gate_liftGRight_uniq
#check gate_eqToHom_app_gleft
#check gate_eqToHom_app_gright
#check gate_RingFragment
#check gate_nf
#check gate_nf_idem
#check gate_nf_sound
#check gate_nf_preserves_fragment
#check gate_nf_complete_fragment
#check gate_nf_step_sound
#check gate_nf_steps_sound
#check gate_rewrite_eval_add_zero
#check gate_rewrite_normalizedConnected_add_zero
#check gate_rewrite_canonicalDescClass_mk_eq_add_zero
#check gate_rewrite_canonicalDesc_eq_add_zero
#check gate_rewrite_quotient_eq_add_zero
#check gate_rewrite_eval_add_zero_surrealModel
#check gate_rewrite_normalizedConnected_add_zero_surrealModel
#check gate_rewrite_canonicalDescClass_mk_eq_add_zero_surrealModel
#check gate_rewrite_canonicalDesc_eq_add_zero_surrealModel
#check gate_rewrite_quotient_eq_add_zero_surrealModel
#check gate_rewrite_eval_add_zero_surrealModelWith_true
#check gate_rewrite_normalizedConnected_add_zero_surrealModelWith_true
#check gate_rewrite_canonicalDesc_eq_add_zero_surrealModelWith_true
#check gate_rewrite_quotient_eq_add_zero_surrealModelWith_true
#check gate_rewrite_canonicalDescClass_mk_eq_add_zero_surrealModelWith_true
#check gate_rewrite_quotient_eq_add_zero_selectTrue
#check gate_rewrite_canonicalDescClass_mk_eq_add_zero_selectTrue
#check gate_add_zero_bundle_active
#check gate_add_zero_bundle_surrealModel
#check gate_add_zero_bundle_selectTrue
#check gate_add_zero_bundle_modelWithTrue
#check gate_selectTrue_rewrite_eval_add_zero
#check gate_selectTrue_rewrite_normalizedConnected_add_zero
#check gate_selectTrue_rewrite_canonicalDesc_eq_add_zero
#check surrealModel_exp
#check surrealModel_log
#check surrealModel_hyperExp
#check surrealModel_hyperLog
#check surrealModelWith_true_exp
#check surrealModelWith_true_log
#check surrealModelWith_true_hyperExp_zero
#check surrealModelWith_true_hyperLog_zero
#check SurrealExpLogSemantics.toModel_active_exp
#check SurrealExpLogSemantics.toModel_active_log
#check SurrealExpLogSemantics.toModel_active_hyperExp
#check SurrealExpLogSemantics.toModel_active_hyperLog
#check SurrealExpLogSemantics.toModel_placeholder_exp
#check SurrealExpLogSemantics.toModel_placeholder_log
#check SurrealExpLogSemantics.toModel_placeholder_hyperExp
#check SurrealExpLogSemantics.toModel_placeholder_hyperLog
#check SurrealExpLogSemantics.not_nontrivial_placeholder

end NameWiringSmoke

end
end Numbers
end Tests
end HeytingLean
