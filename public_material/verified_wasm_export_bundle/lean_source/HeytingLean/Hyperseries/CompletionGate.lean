import HeytingLean.Hyperseries.SurrealDescription
import HeytingLean.Hyperseries.SurrealExpLogSemantics
import HeytingLean.Hyperseries.Eval
import HeytingLean.Hyperseries.Category.RewriteQuiver
import HeytingLean.Hyperseries.Category.Groupoid
import HeytingLean.Hyperseries.Category.NFoldCategoryArrow
import HeytingLean.Hyperseries.Category.OmegaTowerLimit
import HeytingLean.Hyperseries.Category.OmegaTowerLimitUniversal
import HeytingLean.Hyperseries.Category.OmegaTowerLimitGroupoid
import HeytingLean.Hyperseries.Category.OmegaTowerLimitGroupoidUniversal
import HeytingLean.Hyperseries.Category.SemanticsAdapter
import HeytingLean.Hyperseries.Category.CanonicalizationBridge
import HeytingLean.Hyperseries.Category.ContractibilityStrong

namespace HeytingLean
namespace Hyperseries

noncomputable section

theorem gate_realize_describe (a : Surreal) :
    HyperserialDescription.realize (K := Surreal)
      (HyperserialDescription.describe (K := Surreal) a) = a :=
  HyperserialDescription.realize_describe (K := Surreal) a

theorem gate_active_selector_false :
    SurrealExpLogSemantics.activeUseNontrivial = false := by
  simp

theorem gate_active_eq_placeholder :
    SurrealExpLogSemantics.active = SurrealExpLogSemantics.placeholder :=
  SurrealExpLogSemantics.active_eq_placeholder

theorem gate_active_eq_default :
    SurrealExpLogSemantics.active = SurrealExpLogSemantics.default :=
  SurrealExpLogSemantics.active_eq_default

theorem gate_active_eq_select_false :
    SurrealExpLogSemantics.active = SurrealExpLogSemantics.select false :=
  SurrealExpLogSemantics.active_eq_select_false

theorem gate_active_not_nontrivial :
    ¬SurrealExpLogSemantics.Nontrivial SurrealExpLogSemantics.active :=
  SurrealExpLogSemantics.not_nontrivial_active

theorem gate_active_ne_select_true :
    SurrealExpLogSemantics.active ≠ SurrealExpLogSemantics.select true :=
  SurrealExpLogSemantics.active_ne_select_true

theorem gate_eval_default_semantics_eq_active :
    surrealSemanticsDefault = SurrealExpLogSemantics.active :=
  surrealSemanticsDefault_eq_active

theorem gate_eval_model_eq_active :
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active :=
  surrealModel_eq_activeModel

theorem gate_eval_model_eq_false :
    surrealModel = surrealModelWith false :=
  surrealModel_eq_modelWith_false

theorem gate_eval_model_eq_default :
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default :=
  surrealModel_eq_defaultModel

theorem gate_eval_model_eq_placeholder :
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder :=
  surrealModel_eq_placeholderModel

theorem gate_eval_model_with_eq_toModel (b : Bool) :
    surrealModelWith b = SurrealExpLogSemantics.toModel (surrealSemantics b) :=
  surrealModelWith_eq_toModel b

theorem gate_eval_semantics_true_eq_neg :
    surrealSemantics true = SurrealExpLogSemantics.negSemantics :=
  surrealSemantics_true

theorem gate_eval_semantics_true_nontrivial :
    SurrealExpLogSemantics.Nontrivial (surrealSemantics true) := by
  simpa [surrealSemantics] using SurrealExpLogSemantics.nontrivial_select_true

theorem gate_eval_model_false_eq_default :
    surrealModelWith false = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default :=
  surrealModelWith_false

theorem gate_eval_model_false_exp (x : Surreal) :
    (surrealModelWith false).exp x = x := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_false_log (x : Surreal) :
    (surrealModelWith false).log x = x := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_false_hyperExp (α : Ordinal) (x : Surreal) :
    (surrealModelWith false).hyperExp α x = x := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_false_hyperLog (α : Ordinal) (x : Surreal) :
    (surrealModelWith false).hyperLog α x = x := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_true_eq_neg :
    surrealModelWith true = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.negSemantics :=
  surrealModelWith_true

theorem gate_eval_model_true_eq_select_true :
    surrealModelWith true =
      SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true) := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_true_omega :
    HyperserialModel.omega (self := surrealModelWith true) = omegaSurreal := by
  exact surrealModelWith_omega true

theorem gate_eval_model_true_exp (x : Surreal) :
    (surrealModelWith true).exp x = -x := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_true_log (x : Surreal) :
    (surrealModelWith true).log x = -x := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_true_hyperExp_zero (x : Surreal) :
    (surrealModelWith true).hyperExp 0 x = -x := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_true_hyperLog_zero (x : Surreal) :
    (surrealModelWith true).hyperLog 0 x = -x := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_exp_if (b : Bool) (x : Surreal) :
    (surrealModelWith b).exp x = (if b then -x else x) := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_log_if (b : Bool) (x : Surreal) :
    (surrealModelWith b).log x = (if b then -x else x) := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_hyperExp_zero_if (b : Bool) (x : Surreal) :
    (surrealModelWith b).hyperExp 0 x = (if b then -x else x) := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_model_hyperLog_zero_if (b : Bool) (x : Surreal) :
    (surrealModelWith b).hyperLog 0 x = (if b then -x else x) := by
  simp [surrealModelWith, surrealSemantics]

theorem gate_eval_surrealModelWith_true_eq_select_true (e : HExpr) :
    HExpr.eval (surrealModelWith true) e =
      HExpr.eval (SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) e := by
  exact HExpr.eval_eq_of_model_eq gate_eval_model_true_eq_select_true e

theorem gate_canonicalDesc_surrealModelWith_true_eq_select_true (a : HExpr) :
    Category.canonicalDesc (M := surrealModelWith true) a =
      Category.canonicalDesc
        (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) a := by
  simp [Category.canonicalDesc]

theorem gate_canonicalDescClass_mk_surrealModelWith_true_eq_select_true (a : HExpr) :
    Category.canonicalDescClass (M := surrealModelWith true)
      (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModelWith true)) =
    Category.canonicalDescClass
      (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (Quot.mk _ a :
        Category.NormalizedQuotient
          (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) := by
  simp [Category.canonicalDescClass_mk]

theorem gate_surrealModel_exp (x : Surreal) :
    surrealModel.exp x = x := by
  simp [surrealModel]

theorem gate_surrealModel_log (x : Surreal) :
    surrealModel.log x = x := by
  simp [surrealModel]

theorem gate_surrealModel_hyperExp (α : Ordinal) (x : Surreal) :
    surrealModel.hyperExp α x = x := by
  simp [surrealModel]

theorem gate_surrealModel_hyperLog (α : Ordinal) (x : Surreal) :
    surrealModel.hyperLog α x = x := by
  simp [surrealModel]

theorem gate_eval_surrealModel_eq_active (e : HExpr) :
    HExpr.eval surrealModel e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e := by
  exact HExpr.eval_surrealModel_eq_activeModel e

theorem gate_eval_surrealModel_eq_false (e : HExpr) :
    HExpr.eval surrealModel e = HExpr.eval (surrealModelWith false) e := by
  exact HExpr.eval_surrealModel_eq_modelWith_false e

theorem gate_eval_surrealModel_eq_default (e : HExpr) :
    HExpr.eval surrealModel e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e := by
  exact HExpr.eval_surrealModel_eq_defaultModel e

theorem gate_eval_surrealModel_eq_placeholder (e : HExpr) :
    HExpr.eval surrealModel e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
  exact HExpr.eval_surrealModel_eq_placeholderModel e

theorem gate_eval_default_eq_placeholder (e : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
  exact HExpr.eval_defaultModel_eq_placeholderModel e

theorem gate_eval_active_eq_default (e : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e := by
  exact HExpr.eval_activeModel_eq_defaultModel e

theorem gate_eval_active_eq_placeholder (e : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
  exact HExpr.eval_activeModel_eq_placeholderModel e

theorem gate_eval_eq_of_model_eq {K : Type*} [CommRing K]
    {M N : HyperserialModel K} (h : M = N) (e : HExpr) :
    HExpr.eval M e = HExpr.eval N e := by
  exact HExpr.eval_eq_of_model_eq h e

theorem gate_evalQ_eq_of_model_eq {K : Type*} [Field K]
    {M N : HyperserialModel K} (h : M = N) (e : HExprQ) :
    HExprQ.eval M e = HExprQ.eval N e := by
  exact HExprQ.eval_eq_of_model_eq h e

theorem gate_placeholder_exp (x : Surreal) :
    (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).exp x = x := by
  simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]

theorem gate_placeholder_log (x : Surreal) :
    (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).log x = x := by
  simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]

theorem gate_placeholder_hyperExp (α : Ordinal) (x : Surreal) :
    (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).hyperExp α x = x := by
  simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]

theorem gate_placeholder_hyperLog (α : Ordinal) (x : Surreal) :
    (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active).hyperLog α x = x := by
  simp [SurrealExpLogSemantics.active, SurrealExpLogSemantics.toModel]

theorem gate_placeholder_not_nontrivial :
    ¬SurrealExpLogSemantics.Nontrivial SurrealExpLogSemantics.active := by
  exact SurrealExpLogSemantics.not_nontrivial_active

theorem gate_select_true_nontrivial :
    SurrealExpLogSemantics.Nontrivial (SurrealExpLogSemantics.select true) :=
  SurrealExpLogSemantics.nontrivial_select_true

abbrev gate_select_false := SurrealExpLogSemantics.select_false

abbrev gate_select_true := SurrealExpLogSemantics.select_true

abbrev gate_nontrivial_select_iff := SurrealExpLogSemantics.nontrivial_select_iff

abbrev gate_not_nontrivial_select_iff := SurrealExpLogSemantics.not_nontrivial_select_iff

abbrev gate_nontrivial_active_iff := SurrealExpLogSemantics.nontrivial_active_iff

abbrev gate_not_nontrivial_active_iff := SurrealExpLogSemantics.not_nontrivial_active_iff

abbrev gate_toModel_select_false_exp := SurrealExpLogSemantics.toModel_select_false_exp

abbrev gate_toModel_select_false_log := SurrealExpLogSemantics.toModel_select_false_log

abbrev gate_toModel_select_false_hyperExp := SurrealExpLogSemantics.toModel_select_false_hyperExp

abbrev gate_toModel_select_false_hyperLog := SurrealExpLogSemantics.toModel_select_false_hyperLog

abbrev gate_toModel_select_true_exp := SurrealExpLogSemantics.toModel_select_true_exp

abbrev gate_toModel_select_true_log := SurrealExpLogSemantics.toModel_select_true_log

abbrev gate_toModel_select_true_hyperExp_zero := SurrealExpLogSemantics.toModel_select_true_hyperExp_zero

abbrev gate_toModel_select_true_hyperLog_zero := SurrealExpLogSemantics.toModel_select_true_hyperLog_zero

abbrev gate_toModel_select_true_hyperExp_succ := SurrealExpLogSemantics.toModel_select_true_hyperExp_succ

abbrev gate_toModel_select_true_hyperLog_succ := SurrealExpLogSemantics.toModel_select_true_hyperLog_succ

abbrev gate_not_nontrivial_identity := SurrealExpLogSemantics.not_nontrivial_identity

abbrev gate_toCore_identity := SurrealExpLogSemantics.toCore_identity

abbrev gate_HExpr1Obj_ofExpr := Category.HExpr1Obj.ofExpr

theorem gate_HExpr1Obj_expr_ofExpr (e : HExpr) :
    (gate_HExpr1Obj_ofExpr e).expr = e := by
  exact Category.HExpr1Obj.expr_ofExpr e

abbrev gate_ofExpr := Category.HExpr1Obj.ofExpr

abbrev gate_expr_ofExpr := Category.HExpr1Obj.expr_ofExpr

abbrev gate_HRewriteSteps := Category.HRewriteSteps

abbrev gate_hrewrite_steps_refl := Category.HRewriteSteps.refl

abbrev gate_hrewrite_steps_single := @Category.HRewriteSteps.single

abbrev gate_hrewrite_steps_trans := @Category.HRewriteSteps.trans

abbrev gate_hrewrite1_eval_sound := @Category.HRewrite1.eval_sound

abbrev gate_hrewrite_steps_eval_sound := @Category.HRewriteSteps.eval_sound

abbrev gate_refl := Category.HRewriteSteps.refl

abbrev gate_single := @Category.HRewriteSteps.single

abbrev gate_trans := @Category.HRewriteSteps.trans

abbrev gate_eval_sound := @Category.HRewrite1.eval_sound

abbrev gate_quiver_hom_eval_sound := @Category.quiver_hom_eval_sound

abbrev gate_HExprFreeGroupoid := Category.HExprFreeGroupoid

abbrev gate_GObj := Category.GObj

abbrev gate_hrewrite1_toGroupoid := @Category.HRewrite1.toGroupoid

abbrev gate_hrewrite1_toGroupoid_eval_sound := @Category.HRewrite1.toGroupoid_eval_sound

abbrev gate_hrewriteSteps_toGroupoid := @Category.HRewriteSteps.toGroupoid

abbrev gate_hrewriteSteps_toGroupoid_eval_sound := @Category.HRewriteSteps.toGroupoid_eval_sound

abbrev gate_toGroupoid := @Category.HRewrite1.toGroupoid

abbrev gate_toGroupoid_eval_sound := @Category.HRewrite1.toGroupoid_eval_sound

abbrev gate_HCatPkg := Category.HCatPkg

abbrev gate_HCat := Category.HCat

abbrev gate_HCat_src := @Category.src

abbrev gate_HCat_tgt := @Category.tgt

abbrev gate_HCat_edge := @Category.edge

abbrev gate_src := @Category.src

abbrev gate_tgt := @Category.tgt

abbrev gate_edge := @Category.edge

abbrev gate_HDropLeft := Category.HDropLeft

abbrev gate_HDropRight := Category.HDropRight

abbrev gate_HLeftTower := Category.HLeftTower

abbrev gate_HRightTower := Category.HRightTower

abbrev gate_HOmegaLeft := Category.HOmegaLeft

abbrev gate_HOmegaRight := Category.HOmegaRight

abbrev gate_HLeftTowerCone := @Category.HLeftTowerCone

abbrev gate_HRightTowerCone := @Category.HRightTowerCone

abbrev gate_liftLeft := @Category.liftLeft

abbrev gate_liftRight := @Category.liftRight

abbrev gate_liftLeft_fac := @Category.liftLeft_fac

abbrev gate_liftRight_fac := @Category.liftRight_fac

abbrev gate_liftLeft_uniq := @Category.liftLeft_uniq

abbrev gate_liftRight_uniq := @Category.liftRight_uniq

abbrev gate_eqToHom_app_left := @Category.eqToHom_app_left

abbrev gate_eqToHom_app_right := @Category.eqToHom_app_right

abbrev gate_HGCatPkg := Category.HGCatPkg

abbrev gate_HGCat := Category.HGCat

abbrev gate_HGDropLeft := Category.HGDropLeft

abbrev gate_HGDropRight := Category.HGDropRight

abbrev gate_HGLeftTower := Category.HGLeftTower

abbrev gate_HGRightTower := Category.HGRightTower

abbrev gate_HGOmegaLeft := Category.HGOmegaLeft

abbrev gate_HGOmegaRight := Category.HGOmegaRight

abbrev gate_HGLeftTowerCone := @Category.HGLeftTowerCone

abbrev gate_HGRightTowerCone := @Category.HGRightTowerCone

abbrev gate_liftGLeft := @Category.liftGLeft

abbrev gate_liftGRight := @Category.liftGRight

abbrev gate_liftGLeft_fac := @Category.liftGLeft_fac

abbrev gate_liftGRight_fac := @Category.liftGRight_fac

abbrev gate_liftGLeft_uniq := @Category.liftGLeft_uniq

abbrev gate_liftGRight_uniq := @Category.liftGRight_uniq

abbrev gate_eqToHom_app_gleft := @Category.eqToHom_app_gleft

abbrev gate_eqToHom_app_gright := @Category.eqToHom_app_gright

abbrev gate_RingFragment := Category.RingFragment

abbrev gate_nf := Category.nf

abbrev gate_nf_idem := Category.nf_idem

abbrev gate_nf_sound := @Category.nf_sound

abbrev gate_nf_preserves_fragment := @Category.nf_preserves_fragment

abbrev gate_nf_complete_fragment := Category.nf_complete_fragment

abbrev gate_nf_step_sound := @Category.nf_step_sound

abbrev gate_nf_steps_sound := @Category.nf_steps_sound

theorem gate_eval_eq_of_groupoid_hom_generic {K : Type*} [CommRing K]
    (M : HyperserialModel K) {a b : HExpr} (f : Category.GObj a ⟶ Category.GObj b) :
    HExpr.eval M a = HExpr.eval M b := by
  exact Category.eval_eq_of_groupoid_hom (M := M) f

theorem gate_eval_eq_of_connected_generic {K : Type*} [CommRing K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    HExpr.eval M a = HExpr.eval M b := by
  exact Category.eval_eq_of_connected (M := M) h

theorem gate_eval_eq_of_rewrite_steps_generic {K : Type*} [CommRing K]
    (M : HyperserialModel K) {a b : HExpr} (h : Category.HRewriteSteps a b) :
    HExpr.eval M a = HExpr.eval M b := by
  exact Category.eval_eq_of_rewrite_steps (M := M) h

theorem gate_eval_eq_of_rewrite1_generic {K : Type*} [CommRing K]
    (M : HyperserialModel K) {a b : HExpr} (h : Category.HRewrite1 a b) :
    HExpr.eval M a = HExpr.eval M b := by
  exact Category.HRewrite1.eval_sound (M := M) h

theorem gate_connected_of_rewrite1_generic
    {a b : HExpr} (h : Category.HRewrite1 a b) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) :=
  ⟨Category.HRewrite1.toGroupoid h⟩

theorem gate_eval_eq_of_quiver_hom_generic {K : Type*} [CommRing K]
    (M : HyperserialModel K) {X Y : Category.HExpr1Obj}
    (h : X ⟶ Y) :
    HExpr.eval M X.expr = HExpr.eval M Y.expr := by
  exact Category.quiver_hom_eval_sound (M := M) h

theorem gate_canonicalDesc_eq_of_groupoid_hom_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr} (f : Category.GObj a ⟶ Category.GObj b) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.groupoid_hom_implies_canonicalDesc_eq (M := M) f

theorem gate_canonicalDesc_eq_of_connected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.connected_implies_canonicalDesc_eq (M := M) h

theorem gate_normalizedConnected_refl_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (a : HExpr) :
    Category.NormalizedConnected (M := M) a a := by
  exact Category.normalizedConnected_refl (M := M) a

theorem gate_normalizedConnected_symm_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Category.NormalizedConnected (M := M) a b) :
    Category.NormalizedConnected (M := M) b a := by
  exact Category.normalizedConnected_symm (M := M) h

theorem gate_normalizedConnected_trans_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b c : HExpr}
    (hab : Category.NormalizedConnected (M := M) a b)
    (hbc : Category.NormalizedConnected (M := M) b c) :
    Category.NormalizedConnected (M := M) a c := by
  exact Category.normalizedConnected_trans (M := M) hab hbc

abbrev gate_NormalizedQuotient_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) :=
  Category.NormalizedQuotient (M := M)

theorem gate_quotient_eq_of_normalizedConnected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Category.NormalizedConnected (M := M) a b) :
    (Quot.mk _ a : Category.NormalizedQuotient (M := M)) =
      (Quot.mk _ b : Category.NormalizedQuotient (M := M)) := by
  exact Category.quotient_eq_of_normalizedConnected (M := M) h

theorem gate_normalizedConnected_of_quotient_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : (Quot.mk _ a : Category.NormalizedQuotient (M := M)) =
      (Quot.mk _ b : Category.NormalizedQuotient (M := M))) :
    Category.NormalizedConnected (M := M) a b := by
  exact Category.normalizedConnected_of_quotient_eq (M := M) h

theorem gate_canonicalDescClass_eq_of_normalizedConnected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Category.NormalizedConnected (M := M) a b) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient (M := M)) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient (M := M)) := by
  exact Category.canonicalDescClass_eq_of_normalizedConnected (M := M) h

theorem gate_rewrite_steps_implies_normalizedConnected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr} (h : Category.HRewriteSteps a b) :
    Category.NormalizedConnected (M := M) a b := by
  exact Category.rewrite_steps_implies_normalizedConnected (M := M) h

theorem gate_groupoid_hom_implies_canonicalDesc_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr} (f : Category.GObj a ⟶ Category.GObj b) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.groupoid_hom_implies_canonicalDesc_eq (M := M) f

theorem gate_connected_implies_canonicalDesc_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.connected_implies_canonicalDesc_eq (M := M) h

theorem gate_fiber_refl_generic (n : HExpr) :
    Category.FiberTo n n :=
  Category.fiber_refl n

theorem gate_fiber_connected_generic
    {n a b : HExpr} (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) :=
  Category.fiber_connected ha hb

theorem gate_fiber_to_center_generic
    {n a : HExpr} (ha : Category.FiberTo n a) :
    Nonempty (Category.GObj a ⟶ Category.GObj n) :=
  Category.fiber_to_center ha

theorem gate_center_to_fiber_generic
    {n a : HExpr} (ha : Category.FiberTo n a) :
    Nonempty (Category.GObj n ⟶ Category.GObj a) :=
  Category.center_to_fiber ha

theorem gate_eval_eq_of_fiber_generic {K : Type*} [CommRing K]
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    HExpr.eval M a = HExpr.eval M b := by
  exact Category.eval_eq_of_fiber (M := M) ha hb

theorem gate_normalizedConnected_of_fiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    Category.NormalizedConnected (M := M) a b := by
  exact Category.normalizedConnected_of_fiber (M := M) ha hb

theorem gate_canonicalDesc_eq_of_fiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_fiber (M := M) ha hb

theorem gate_quotient_eq_of_fiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    (Quot.mk _ a : Category.NormalizedQuotient (M := M)) =
      (Quot.mk _ b : Category.NormalizedQuotient (M := M)) := by
  exact Category.quotient_eq_of_fiber (M := M) ha hb

theorem gate_canonicalDescClass_eq_of_fiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient (M := M)) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient (M := M)) := by
  exact Category.canonicalDescClass_eq_of_fiber (M := M) ha hb

abbrev gate_normalizedConnected_of_uniqueNF_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) :=
  @Category.normalizedConnected_of_uniqueNF K _ _ M

abbrev gate_quotient_eq_of_uniqueNF_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) :=
  @Category.quotient_eq_of_uniqueNF K _ _ M

abbrev gate_canonicalDesc_eq_of_uniqueNF_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) :=
  @Category.canonicalDesc_eq_of_uniqueNF K _ _ M

abbrev gate_canonicalDesc_nf_eq_of_uniqueNF_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) :=
  @Category.canonicalDesc_nf_eq_of_uniqueNF K _ _ M

abbrev gate_canonicalDescClass_eq_of_uniqueNF_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) :=
  @Category.canonicalDescClass_eq_of_uniqueNF K _ _ M

abbrev gate_canonicalDescClass_mk_eq_of_uniqueNF_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) :=
  @Category.canonicalDescClass_mk_eq_of_uniqueNF K _ _ M

theorem gate_normalizedConnected_of_rewrite_steps_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr} (h : Category.HRewriteSteps a b) :
    Category.NormalizedConnected (M := M) a b := by
  exact Category.rewrite_steps_implies_normalizedConnected (M := M) h

theorem gate_canonicalDesc_eq_iff_normalizedConnected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (a b : HExpr) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      Category.NormalizedConnected (M := M) a b := by
  exact Category.canonicalDesc_eq_iff_normalizedConnected (M := M) a b

theorem gate_quotient_eq_iff_normalizedConnected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (a b : HExpr) :
    ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) ↔
      Category.NormalizedConnected (M := M) a b := by
  exact Category.quotient_eq_iff_normalizedConnected (M := M) a b

theorem gate_quotient_eq_iff_canonicalDescClass_mk_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (a b : HExpr) :
    ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) ↔
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.quotient_eq_iff_canonicalDescClass_mk_eq (M := M) a b

theorem gate_canonicalDescClass_mk_eq_iff_normalizedConnected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (a b : HExpr) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ↔
      Category.NormalizedConnected (M := M) a b := by
  exact Category.canonicalDescClass_mk_eq_iff_normalizedConnected (M := M) a b

theorem gate_normalizedConnected_of_canonicalDescClass_mk_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :
    Category.NormalizedConnected (M := M) a b := by
  exact Category.normalizedConnected_of_canonicalDescClass_mk_eq (M := M) h

theorem gate_quotient_eq_of_canonicalDescClass_mk_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :
    (Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.quotient_eq_of_canonicalDescClass_mk_eq (M := M) h

theorem gate_canonicalDescClass_mk_eq_of_quotient_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : (Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.canonicalDescClass_mk_eq_of_quotient_eq (M := M) h

theorem gate_canonicalDescClass_mk_eq_of_rewrite_steps_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr} (h : Category.HRewriteSteps a b) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.canonicalDescClass_mk_eq_of_rewrite_steps (M := M) h

theorem gate_canonicalDescClass_mk_eq_of_groupoid_hom_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr} (f : Category.GObj a ⟶ Category.GObj b) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.canonicalDescClass_mk_eq_of_groupoid_hom (M := M) f

theorem gate_canonicalDescClass_mk_eq_of_connected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.canonicalDescClass_mk_eq_of_connected (M := M) h

theorem gate_quotient_eq_of_rewrite_steps_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr} (h : Category.HRewriteSteps a b) :
    (Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact (gate_quotient_eq_iff_normalizedConnected_generic (M := M) a b).2
    (gate_normalizedConnected_of_rewrite_steps_generic (M := M) h)

theorem gate_quotient_eq_of_canonicalDesc_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    (Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.quotient_eq_of_canonicalDesc_eq (M := M) h

theorem gate_canonicalDesc_eq_of_quotient_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : (Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_quotient_eq (M := M) h

theorem gate_canonicalDesc_eq_iff_quotient_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (a b : HExpr) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.canonicalDesc_eq_iff_quotient_eq (M := M) a b

theorem gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.canonicalDescClass_mk_eq_of_canonicalDesc_eq (M := M) h

theorem gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_canonicalDescClass_mk_eq (M := M) h

theorem gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (a b : HExpr) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ↔
      Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDescClass_mk_eq_iff_canonicalDesc_eq (M := M) a b

theorem gate_rewriteComplete_of_valuation_bridge_generic
    {K : Type*} [CommRing K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν) :
    Category.RewriteComplete (M := M) := by
  exact Category.rewriteComplete_of_valuation_bridge (M := M) ν hν hcompleteν

theorem gate_eval_eq_of_canonicalDesc_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {a b : HExpr}
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    HExpr.eval M a = HExpr.eval M b := by
  exact Category.eval_eq_of_canonicalDesc_eq (M := M) h

theorem gate_connected_of_canonicalDesc_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    {a b : HExpr}
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.connected_of_canonicalDesc_eq (M := M) hcomplete h

theorem gate_canonicalDesc_eq_iff_connected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    (a b : HExpr) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.canonicalDesc_eq_iff_connected (M := M) hcomplete a b

theorem gate_canonicalFiber_connected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    {d : HDesc K}
    (x y : Category.CanonicalFiber (M := M) d) :
    Nonempty (Category.GObj x.1 ⟶ Category.GObj y.1) := by
  exact Category.canonicalFiber_connected (M := M) hcomplete x y

theorem gate_canonicalFiber_contractible_at_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    {d : HDesc K}
    (c : Category.CanonicalFiber (M := M) d) :
    ∀ x : Category.CanonicalFiber (M := M) d, Nonempty (Category.GObj x.1 ⟶ Category.GObj c.1) := by
  exact Category.canonicalFiber_contractible_at (M := M) hcomplete c

theorem gate_canonicalFiber_connected_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {d : HDesc K}
    (x y : Category.CanonicalFiber (M := M) d) :
    Nonempty (Category.GObj x.1 ⟶ Category.GObj y.1) := by
  exact Category.canonicalFiber_connected_of_valuation (M := M) ν hν hcompleteν x y

theorem gate_canonicalFiber_contractible_at_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {d : HDesc K}
    (c : Category.CanonicalFiber (M := M) d) :
    ∀ x : Category.CanonicalFiber (M := M) d, Nonempty (Category.GObj x.1 ⟶ Category.GObj c.1) := by
  exact Category.canonicalFiber_contractible_at_of_valuation (M := M) ν hν hcompleteν c

theorem gate_canonicalDesc_eq_of_canonicalValuationFiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : Category.CanonicalValuationFiber (M := M) ν d e) :
    Category.canonicalDesc (M := M) x.1 = Category.canonicalDesc (M := M) y.1 := by
  exact Category.canonicalDesc_eq_of_canonicalValuationFiber (M := M) ν x y

theorem gate_valuation_eq_of_canonicalValuationFiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : Category.CanonicalValuationFiber (M := M) ν d e) :
    ν x.1 = ν y.1 := by
  exact Category.valuation_eq_of_canonicalValuationFiber (M := M) ν x y

theorem gate_eval_eq_of_canonicalValuationFiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : Category.CanonicalValuationFiber (M := M) ν d e) :
    HExpr.eval M x.1 = HExpr.eval M y.1 := by
  exact Category.eval_eq_of_canonicalValuationFiber (M := M) ν x y

theorem gate_canonicalValuationFiber_connected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {d : HDesc K} {e : ℤ}
    (x y : Category.CanonicalValuationFiber (M := M) ν d e) :
    Nonempty (Category.GObj x.1 ⟶ Category.GObj y.1) := by
  exact Category.canonicalValuationFiber_connected (M := M) ν hcompleteν x y

theorem gate_canonicalValuationFiber_contractible_at_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {d : HDesc K} {e : ℤ}
    (c : Category.CanonicalValuationFiber (M := M) ν d e) :
    ∀ x : Category.CanonicalValuationFiber (M := M) ν d e,
      Nonempty (Category.GObj x.1 ⟶ Category.GObj c.1) := by
  exact Category.canonicalValuationFiber_contractible_at (M := M) ν hcompleteν c

theorem gate_normalizedConnected_of_canonicalValuationFiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : Category.CanonicalValuationFiber (M := M) ν d e) :
    Category.NormalizedConnected (M := M) x.1 y.1 := by
  exact Category.normalizedConnected_of_canonicalValuationFiber (M := M) ν x y

theorem gate_quotient_eq_of_canonicalValuationFiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : Category.CanonicalValuationFiber (M := M) ν d e) :
    (Quot.mk _ x.1 : Category.NormalizedQuotient (M := M)) =
      (Quot.mk _ y.1 : Category.NormalizedQuotient (M := M)) := by
  exact Category.quotient_eq_of_canonicalValuationFiber (M := M) ν x y

theorem gate_canonicalDescClass_eq_of_canonicalValuationFiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : Category.CanonicalValuationFiber (M := M) ν d e) :
    Category.canonicalDescClass (M := M) (Quot.mk _ x.1 : Category.NormalizedQuotient (M := M)) =
      Category.canonicalDescClass (M := M) (Quot.mk _ y.1 : Category.NormalizedQuotient (M := M)) := by
  exact Category.canonicalDescClass_eq_of_canonicalValuationFiber (M := M) ν x y

theorem gate_normalizedConnected_implies_connected_nf_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    {a b : HExpr} (h : Category.NormalizedConnected (M := M) a b) :
    Nonempty (Category.GObj (Category.nf a) ⟶ Category.GObj (Category.nf b)) := by
  exact Category.normalizedConnected_implies_connected_nf (M := M) hcomplete h

theorem gate_normalizedConnected_iff_connected_nf_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    (a b : HExpr) :
    Category.NormalizedConnected (M := M) a b ↔
      Nonempty (Category.GObj (Category.nf a) ⟶ Category.GObj (Category.nf b)) := by
  exact Category.normalizedConnected_iff_connected_nf (M := M) hcomplete a b

theorem gate_canonicalDesc_nf_eq_iff_connected_nf_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    (a b : HExpr) :
    Category.canonicalDesc (M := M) (Category.nf a) = Category.canonicalDesc (M := M) (Category.nf b) ↔
      Nonempty (Category.GObj (Category.nf a) ⟶ Category.GObj (Category.nf b)) := by
  exact Category.canonicalDesc_nf_eq_iff_connected_nf (M := M) hcomplete a b

theorem gate_connected_nf_of_canonicalDesc_nf_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    {a b : HExpr}
    (h : Category.canonicalDesc (M := M) (Category.nf a) =
      Category.canonicalDesc (M := M) (Category.nf b)) :
    Nonempty (Category.GObj (Category.nf a) ⟶ Category.GObj (Category.nf b)) := by
  exact Category.connected_nf_of_canonicalDesc_nf_eq (M := M) hcomplete h

theorem gate_canonicalDesc_nf_eq_of_connected_nf_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    {a b : HExpr}
    (h : Nonempty (Category.GObj (Category.nf a) ⟶ Category.GObj (Category.nf b))) :
    Category.canonicalDesc (M := M) (Category.nf a) = Category.canonicalDesc (M := M) (Category.nf b) := by
  exact Category.canonicalDesc_nf_eq_of_connected_nf (M := M) hcomplete h

theorem gate_connected_of_shared_fiber_generic
    {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.connected_of_shared_fiber (ha := ha) (hb := hb)

theorem gate_connected_nf_of_shared_fiber_generic
    {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    Nonempty (Category.GObj (Category.nf a) ⟶ Category.GObj (Category.nf b)) := by
  exact Category.connected_nf_of_shared_fiber (ha := ha) (hb := hb)

theorem gate_canonicalDesc_eq_of_shared_fiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_shared_fiber (M := M) (ha := ha) (hb := hb)

theorem gate_canonicalDesc_eq_nf_of_shared_fiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    Category.canonicalDesc (M := M) (Category.nf a) = Category.canonicalDesc (M := M) (Category.nf b) := by
  exact Category.canonicalDesc_eq_nf_of_shared_fiber (M := M) (ha := ha) (hb := hb)

theorem gate_quotient_eq_of_shared_fiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    (Quot.mk _ a : Category.NormalizedQuotient (M := M)) =
      (Quot.mk _ b : Category.NormalizedQuotient (M := M)) := by
  exact Category.quotient_eq_of_shared_fiber (M := M) (ha := ha) (hb := hb)

theorem gate_canonicalDescClass_mk_eq_of_shared_fiber_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : Category.FiberTo n a) (hb : Category.FiberTo n b) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient (M := M)) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient (M := M)) := by
  exact Category.canonicalDescClass_mk_eq_of_shared_fiber (M := M) (ha := ha) (hb := hb)

theorem gate_connected_of_canonicalDesc_eq_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    {a b : HExpr}
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.connected_of_canonicalDesc_eq (M := M) hcomplete h

theorem gate_canonicalDesc_eq_iff_connected_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    (a b : HExpr) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.canonicalDesc_eq_iff_connected (M := M) hcomplete a b

theorem gate_canonicalDesc_eq_of_connected_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    {a b : HExpr} (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_connected (M := M) hcomplete h

theorem gate_quotient_eq_iff_connected_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    (a b : HExpr) :
    ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) ↔
      Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.quotient_eq_iff_connected (M := M) hcomplete a b

theorem gate_canonicalDesc_eq_iff_quotient_eq_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    (a b : HExpr) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.canonicalDesc_eq_iff_quotient_eq_of_rewriteComplete (M := M) hcomplete a b

theorem gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (hcomplete : Category.RewriteComplete (M := M))
    (a b : HExpr) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ↔
      Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_rewriteComplete
    (M := M) hcomplete a b

abbrev gate_canonicalDescClass_mk_eq_iff_connected_nf_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_iff_connected_nf K _ _

abbrev gate_canonicalDescClass_mk_eq_iff_normalizedConnected_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_iff_normalizedConnected_of_rewriteComplete K _ _

abbrev gate_normalizedConnected_of_canonicalDescClass_mk_eq_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.normalizedConnected_of_canonicalDescClass_mk_eq_of_rewriteComplete K _ _

abbrev gate_canonicalDescClass_mk_eq_of_normalizedConnected_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_of_normalizedConnected_of_rewriteComplete K _ _

abbrev gate_canonicalDescClass_mk_eq_iff_connected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_iff_connected K _ _

abbrev gate_connected_nf_of_canonicalDescClass_mk_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.connected_nf_of_canonicalDescClass_mk_eq K _ _

abbrev gate_connected_of_canonicalDescClass_mk_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.connected_of_canonicalDescClass_mk_eq K _ _

abbrev gate_canonicalDescClass_mk_eq_of_connected_nf_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_of_connected_nf K _ _

abbrev gate_quotient_eq_of_connected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.quotient_eq_of_connected K _ _

abbrev gate_connected_of_quotient_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.connected_of_quotient_eq K _ _

abbrev gate_quotient_eq_iff_connected_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.quotient_eq_iff_connected K _ _

abbrev gate_canonicalDescClass_mk_eq_iff_quotient_eq_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_iff_quotient_eq K _ _

abbrev gate_canonicalDesc_eq_of_quotient_eq_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDesc_eq_of_quotient_eq_of_rewriteComplete K _ _

abbrev gate_quotient_eq_of_canonicalDesc_eq_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.quotient_eq_of_canonicalDesc_eq_of_rewriteComplete K _ _

abbrev gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_rewriteComplete K _ _

abbrev gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_rewriteComplete_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_rewriteComplete K _ _

abbrev gate_canonicalDescClass_mk_eq_iff_normalizedConnected_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_iff_normalizedConnected_of_valuation K _ _

abbrev gate_normalizedConnected_of_canonicalDescClass_mk_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.normalizedConnected_of_canonicalDescClass_mk_eq_of_valuation K _ _

abbrev gate_canonicalDescClass_mk_eq_of_normalizedConnected_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_of_normalizedConnected_of_valuation K _ _

abbrev gate_canonicalDescClass_mk_eq_iff_connected_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_iff_connected_of_valuation K _ _

abbrev gate_connected_of_canonicalDescClass_mk_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.connected_of_canonicalDescClass_mk_eq_of_valuation K _ _

abbrev gate_canonicalDescClass_mk_eq_of_connected_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_of_connected_of_valuation K _ _

abbrev gate_quotient_eq_of_connected_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.quotient_eq_of_connected_of_valuation K _ _

abbrev gate_connected_of_quotient_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.connected_of_quotient_eq_of_valuation K _ _

abbrev gate_canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_of_quotient_eq_of_valuation K _ _

abbrev gate_quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.quotient_eq_of_canonicalDescClass_mk_eq_of_valuation K _ _

abbrev gate_canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation K _ _

abbrev gate_canonicalDesc_eq_of_quotient_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDesc_eq_of_quotient_eq_of_valuation K _ _

abbrev gate_quotient_eq_of_canonicalDesc_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.quotient_eq_of_canonicalDesc_eq_of_valuation K _ _

abbrev gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation K _ _

abbrev gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation K _ _

abbrev gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_index K _ _

abbrev gate_canonicalDescClass_mk_eq_iff_connected_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_iff_connected_of_valuation_index K _ _

abbrev gate_connected_of_canonicalDescClass_mk_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.connected_of_canonicalDescClass_mk_eq_of_valuation_index K _ _

abbrev gate_canonicalDescClass_mk_eq_of_connected_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_of_connected_of_valuation_index K _ _

abbrev gate_quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_index K _ _

abbrev gate_canonicalDesc_eq_iff_connected_class_quotient_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDesc_eq_iff_connected_class_quotient_of_valuation_index K _ _

abbrev gate_canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_index K _ _

abbrev gate_quotient_eq_iff_connected_class_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K] :=
  @Category.quotient_eq_iff_connected_class_of_valuation_index K _ _

theorem gate_canonicalDesc_eq_iff_connected_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.canonicalDesc_eq_iff_connected_of_valuation (M := M) ν hν hcompleteν a b

theorem gate_connected_of_canonicalDesc_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.connected_of_canonicalDesc_eq_of_valuation (M := M) ν hν hcompleteν h

theorem gate_canonicalDesc_eq_of_connected_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_connected_of_valuation (M := M) ν hν hcompleteν h

theorem gate_quotient_eq_iff_connected_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) ↔
      Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.quotient_eq_iff_connected_of_valuation (M := M) ν hν hcompleteν a b

theorem gate_canonicalDesc_eq_iff_quotient_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.canonicalDesc_eq_iff_quotient_eq_of_valuation (M := M) ν hν hcompleteν a b

theorem gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ↔
      Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation
    (M := M) ν hν hcompleteν a b

abbrev gate_canonicalDesc_eq_iff_connected_class_quotient_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν) :=
  Category.canonicalDesc_eq_iff_connected_class_quotient_of_valuation
    (M := M) ν hν hcompleteν

abbrev gate_canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν) :=
  Category.canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation
    (M := M) ν hν hcompleteν

abbrev gate_quotient_eq_iff_connected_class_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν) :=
  Category.quotient_eq_iff_connected_class_of_valuation
    (M := M) ν hν hcompleteν

abbrev gate_canonicalDesc_class_quotient_connected_bundle_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν) :=
  Category.canonicalDesc_class_quotient_connected_bundle_of_valuation
    (M := M) ν hν hcompleteν

abbrev gate_connected_class_quotient_of_canonicalDesc_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :=
  Category.connected_class_quotient_of_canonicalDesc_eq_of_valuation
    (M := M) ν hν hcompleteν h

abbrev gate_canonicalDesc_eq_of_connected_class_quotient_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M))) :=
  Category.canonicalDesc_eq_of_connected_class_quotient_of_valuation
    (M := M) ν hν hcompleteν h

abbrev gate_connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :=
  Category.connected_quotient_of_canonicalDescClass_mk_eq_of_valuation
    (M := M) ν hν hcompleteν h

abbrev gate_canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M))) :=
  Category.canonicalDescClass_mk_eq_of_connected_quotient_of_valuation
    (M := M) ν hν hcompleteν h

abbrev gate_connected_class_of_quotient_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M))) :=
  Category.connected_class_of_quotient_eq_of_valuation
    (M := M) ν hν hcompleteν h

abbrev gate_quotient_eq_of_connected_class_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :=
  Category.quotient_eq_of_connected_class_of_valuation
    (M := M) ν hν hcompleteν h

theorem gate_canonicalDesc_eq_iff_connected_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.canonicalDesc_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν ha hb

theorem gate_connected_of_canonicalDesc_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (_hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.connected_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν hcompleteν h ha hb

theorem gate_canonicalDesc_eq_of_connected_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_connected_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_quotient_eq_of_canonicalDesc_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (_hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (_hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.quotient_eq_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν h ha hb

theorem gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (_hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (_hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν h ha hb

theorem gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ↔
      Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb

theorem gate_quotient_eq_iff_connected_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e) :
    ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) ↔
      Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.quotient_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν ha hb

theorem gate_connected_of_quotient_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M))) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) := by
  exact Category.connected_of_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_quotient_eq_of_connected_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.quotient_eq_of_connected_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_canonicalDesc_eq_iff_quotient_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.canonicalDesc_eq_iff_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb

theorem gate_canonicalDesc_eq_of_quotient_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M))) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ↔
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb

theorem gate_canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M))) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_canonicalDesc_class_quotient_connected_bundle_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e) :
    (Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) ∧
    (Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ↔
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M))) ∧
    (((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) ↔
      Nonempty (Category.GObj a ⟶ Category.GObj b)) := by
  exact Category.canonicalDesc_class_quotient_connected_bundle_of_valuation_index
    (M := M) ν hν hcompleteν ha hb

theorem gate_connected_class_quotient_of_canonicalDesc_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.connected_class_quotient_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_canonicalDesc_eq_of_connected_class_quotient_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M))) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_connected_class_quotient_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M))) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_connected_class_of_quotient_eq_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M))) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.connected_class_of_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_quotient_eq_of_connected_class_of_valuation_index_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ} (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :
    ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.quotient_eq_of_connected_class_of_valuation_index
    (M := M) ν hν hcompleteν ha hb h

theorem gate_canonicalDesc_class_quotient_connected_bundle_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :
    (Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b ↔
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) ∧
    (Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ↔
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M))) ∧
    (((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) ↔
      Nonempty (Category.GObj a ⟶ Category.GObj b)) := by
  exact Category.canonicalDesc_class_quotient_connected_bundle_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

theorem gate_connected_class_quotient_of_canonicalDesc_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.connected_class_quotient_of_canonicalDesc_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

theorem gate_canonicalDesc_eq_of_connected_class_quotient_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M))) :
    Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b := by
  exact Category.canonicalDesc_eq_of_connected_class_quotient_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

theorem gate_connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

theorem gate_canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      ((Quot.mk _ a : Category.NormalizedQuotient M) =
        (Quot.mk _ b : Category.NormalizedQuotient M))) :
    Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

theorem gate_connected_class_of_quotient_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M))) :
    Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M) := by
  exact Category.connected_class_of_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

theorem gate_quotient_eq_of_connected_class_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b) ∧
      Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
        Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :
    ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M)) := by
  exact Category.quotient_eq_of_connected_class_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDesc_eq_iff_connected_class_quotient_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :=
  Category.canonicalDesc_eq_iff_connected_class_quotient_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

abbrev gate_canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :=
  Category.canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

abbrev gate_quotient_eq_iff_connected_class_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :=
  Category.quotient_eq_iff_connected_class_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

abbrev gate_connected_of_canonicalDesc_eq_of_valuation_sameIndex_core_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (hdesc : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :=
  Category.connected_of_canonicalDesc_eq_of_valuation_sameIndex_core
    (M := M) ν hcompleteν hidx hdesc

abbrev gate_quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {a b : HExpr} (hidx : ν a = ν b)
    (hdesc : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :=
  Category.quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core
    (M := M) ν hidx hdesc

abbrev gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {a b : HExpr} (hidx : ν a = ν b)
    (hdesc : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :=
  Category.canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core
    (M := M) ν hidx hdesc

abbrev gate_canonicalDesc_eq_iff_connected_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :=
  Category.canonicalDesc_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

abbrev gate_connected_of_canonicalDesc_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :=
  Category.connected_of_canonicalDesc_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDesc_eq_of_connected_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :=
  Category.canonicalDesc_eq_of_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDescClass_mk_eq_iff_connected_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :=
  Category.canonicalDescClass_mk_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

abbrev gate_connected_of_canonicalDescClass_mk_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :=
  Category.connected_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDescClass_mk_eq_of_connected_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :=
  Category.canonicalDescClass_mk_eq_of_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_quotient_eq_iff_connected_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :=
  Category.quotient_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

abbrev gate_connected_of_quotient_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M))) :=
  Category.connected_of_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_quotient_eq_of_connected_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :=
  Category.quotient_eq_of_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :=
  Category.canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

abbrev gate_quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :=
  Category.quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M))) :=
  Category.canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :=
  Category.canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

abbrev gate_canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :=
  Category.canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :=
  Category.canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDesc_eq_iff_quotient_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :=
  Category.canonicalDesc_eq_iff_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

abbrev gate_canonicalDesc_eq_of_quotient_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : ((Quot.mk _ a : Category.NormalizedQuotient M) =
      (Quot.mk _ b : Category.NormalizedQuotient M))) :=
  Category.canonicalDesc_eq_of_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b)
    (h : Category.canonicalDesc (M := M) a = Category.canonicalDesc (M := M) b) :=
  Category.quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

abbrev gate_canonicalDesc_nf_eq_iff_connected_nf_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :=
  Category.canonicalDesc_nf_eq_iff_connected_nf_of_valuation
    (M := M) ν hν hcompleteν a b

abbrev gate_normalizedConnected_iff_connected_nf_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :=
  Category.normalizedConnected_iff_connected_nf_of_valuation
    (M := M) ν hν hcompleteν a b

abbrev gate_canonicalDescClass_mk_eq_iff_connected_nf_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :=
  Category.canonicalDescClass_mk_eq_iff_connected_nf_of_valuation
    (M := M) ν hν hcompleteν a b

abbrev gate_connected_nf_of_canonicalDescClass_mk_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Category.canonicalDescClass (M := M) (Quot.mk _ a : Category.NormalizedQuotient M) =
      Category.canonicalDescClass (M := M) (Quot.mk _ b : Category.NormalizedQuotient M)) :=
  Category.connected_nf_of_canonicalDescClass_mk_eq_of_valuation
    (M := M) ν hν hcompleteν h

abbrev gate_canonicalDescClass_mk_eq_of_connected_nf_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (Category.GObj (Category.nf a) ⟶ Category.GObj (Category.nf b))) :=
  Category.canonicalDescClass_mk_eq_of_connected_nf_of_valuation
    (M := M) ν hν hcompleteν h

abbrev gate_connected_nf_of_canonicalDesc_nf_eq_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Category.canonicalDesc (M := M) (Category.nf a) =
      Category.canonicalDesc (M := M) (Category.nf b)) :=
  Category.connected_nf_of_canonicalDesc_nf_eq_of_valuation
    (M := M) ν hν hcompleteν h

abbrev gate_canonicalDesc_nf_eq_of_connected_nf_of_valuation_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : Category.RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (Category.GObj (Category.nf a) ⟶ Category.GObj (Category.nf b))) :=
  Category.canonicalDesc_nf_eq_of_connected_nf_of_valuation
    (M := M) ν hν hcompleteν h

theorem gate_active_canonicalDesc_eq_of_connected
    {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    Category.canonicalDesc
      (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) a =
      Category.canonicalDesc
        (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) b := by
  exact gate_canonicalDesc_eq_of_connected_generic
    (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) h

theorem gate_selectTrue_canonicalDesc_eq_of_connected
    {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    Category.canonicalDesc
      (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) a =
      Category.canonicalDesc
        (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) b := by
  exact gate_canonicalDesc_eq_of_connected_generic
    (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) h

theorem gate_modelWithTrue_canonicalDesc_eq_of_connected
    {a b : HExpr}
    (h : Nonempty (Category.GObj a ⟶ Category.GObj b)) :
    Category.canonicalDesc (M := surrealModelWith true) a =
      Category.canonicalDesc (M := surrealModelWith true) b := by
  exact gate_canonicalDesc_eq_of_connected_generic (M := surrealModelWith true) h

theorem gate_rewrite_eval_add_zero_generic {K : Type*} [CommRing K]
    (M : HyperserialModel K) (a : HExpr) :
    HExpr.eval M (ExprC.add a (ExprC.C (0 : ℤ))) = HExpr.eval M a := by
  exact gate_eval_eq_of_rewrite_steps_generic (M := M)
    (h := Category.HRewriteSteps.single (Category.HRewrite1.add_zero_right a))

theorem gate_rewrite_normalizedConnected_add_zero_generic
    {K : Type*} [CommRing K] [HyperserialDescription K]
    (M : HyperserialModel K) (a : HExpr) :
    Category.NormalizedConnected
      (M := M)
      (ExprC.add a (ExprC.C (0 : ℤ))) a := by
  exact gate_normalizedConnected_of_rewrite_steps_generic (M := M)
    (h := Category.HRewriteSteps.single (Category.HRewrite1.add_zero_right a))

theorem gate_rewrite_eval_add_zero (a : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) a := by
  exact gate_rewrite_eval_add_zero_generic
    (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) a

theorem gate_rewrite_normalizedConnected_add_zero (a : HExpr) :
    Category.NormalizedConnected
      (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (ExprC.add a (ExprC.C (0 : ℤ))) a := by
  exact gate_rewrite_normalizedConnected_add_zero_generic
    (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) a

theorem gate_rewrite_canonicalDescClass_mk_eq_add_zero (a : HExpr) :
    Category.canonicalDescClass (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
        Category.NormalizedQuotient (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)) =
    Category.canonicalDescClass (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (Quot.mk _ a :
        Category.NormalizedQuotient (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)) := by
  exact gate_canonicalDescClass_mk_eq_of_connected_generic
    (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
    (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))

theorem gate_rewrite_canonicalDesc_eq_add_zero (a : HExpr) :
    Category.canonicalDesc (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (ExprC.add a (ExprC.C (0 : ℤ))) =
    Category.canonicalDesc (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) a := by
  exact gate_canonicalDesc_eq_of_connected_generic
    (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
    (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))

theorem gate_rewrite_quotient_eq_add_zero (a : HExpr) :
    (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
      Category.NormalizedQuotient (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)) =
    (Quot.mk _ a :
      Category.NormalizedQuotient (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)) := by
  exact gate_quotient_eq_of_canonicalDescClass_mk_eq_generic
    (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
    (h := gate_rewrite_canonicalDescClass_mk_eq_add_zero a)

theorem gate_rewrite_eval_add_zero_surrealModel (a : HExpr) :
    HExpr.eval surrealModel (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval surrealModel a := by
  exact gate_rewrite_eval_add_zero_generic (M := surrealModel) a

theorem gate_rewrite_normalizedConnected_add_zero_surrealModel (a : HExpr) :
    Category.NormalizedConnected
      (M := surrealModel)
      (ExprC.add a (ExprC.C (0 : ℤ))) a := by
  exact gate_rewrite_normalizedConnected_add_zero_generic (M := surrealModel) a

theorem gate_rewrite_canonicalDescClass_mk_eq_add_zero_surrealModel (a : HExpr) :
    Category.canonicalDescClass (M := surrealModel)
      (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
        Category.NormalizedQuotient (M := surrealModel)) =
    Category.canonicalDescClass (M := surrealModel)
      (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModel)) := by
  exact gate_canonicalDescClass_mk_eq_of_connected_generic
    (M := surrealModel)
    (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))

theorem gate_rewrite_canonicalDesc_eq_add_zero_surrealModel (a : HExpr) :
    Category.canonicalDesc (M := surrealModel) (ExprC.add a (ExprC.C (0 : ℤ))) =
      Category.canonicalDesc (M := surrealModel) a := by
  exact gate_canonicalDesc_eq_of_connected_generic
    (M := surrealModel)
    (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))

theorem gate_rewrite_quotient_eq_add_zero_surrealModel (a : HExpr) :
    (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
      Category.NormalizedQuotient (M := surrealModel)) =
    (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModel)) := by
  exact gate_quotient_eq_of_canonicalDescClass_mk_eq_generic
    (M := surrealModel)
    (h := gate_rewrite_canonicalDescClass_mk_eq_add_zero_surrealModel a)

theorem gate_selectTrue_rewrite_eval_add_zero (a : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval (SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) a := by
  exact gate_rewrite_eval_add_zero_generic
    (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) a

theorem gate_selectTrue_rewrite_normalizedConnected_add_zero (a : HExpr) :
    Category.NormalizedConnected
      (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (ExprC.add a (ExprC.C (0 : ℤ))) a := by
  exact gate_rewrite_normalizedConnected_add_zero_generic
    (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) a

theorem gate_selectTrue_rewrite_canonicalDesc_eq_add_zero (a : HExpr) :
    Category.canonicalDesc (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (ExprC.add a (ExprC.C (0 : ℤ))) =
    Category.canonicalDesc (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) a := by
  exact gate_canonicalDesc_eq_of_connected_generic
    (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
    (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))

theorem gate_rewrite_eval_add_zero_surrealModelWith_true (a : HExpr) :
    HExpr.eval (surrealModelWith true) (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval (surrealModelWith true) a := by
  exact gate_rewrite_eval_add_zero_generic (M := surrealModelWith true) a

theorem gate_rewrite_normalizedConnected_add_zero_surrealModelWith_true (a : HExpr) :
    Category.NormalizedConnected
      (M := surrealModelWith true)
      (ExprC.add a (ExprC.C (0 : ℤ))) a := by
  exact gate_rewrite_normalizedConnected_add_zero_generic (M := surrealModelWith true) a

theorem gate_rewrite_canonicalDesc_eq_add_zero_surrealModelWith_true (a : HExpr) :
    Category.canonicalDesc (M := surrealModelWith true) (ExprC.add a (ExprC.C (0 : ℤ))) =
      Category.canonicalDesc (M := surrealModelWith true) a := by
  exact gate_canonicalDesc_eq_of_connected_generic
    (M := surrealModelWith true)
    (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))

theorem gate_rewrite_quotient_eq_add_zero_surrealModelWith_true
    (a : HExpr) :
    (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
      Category.NormalizedQuotient (M := surrealModelWith true)) =
    (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModelWith true)) := by
  have hclass :
      Category.canonicalDescClass (M := surrealModelWith true)
        (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
          Category.NormalizedQuotient (M := surrealModelWith true)) =
      Category.canonicalDescClass (M := surrealModelWith true)
        (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModelWith true)) := by
    exact gate_canonicalDescClass_mk_eq_of_connected_generic
      (M := surrealModelWith true)
      (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))
  exact gate_quotient_eq_of_canonicalDescClass_mk_eq_generic
    (M := surrealModelWith true)
    (h := hclass)

theorem gate_rewrite_canonicalDescClass_mk_eq_add_zero_surrealModelWith_true (a : HExpr) :
    Category.canonicalDescClass (M := surrealModelWith true)
      (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
        Category.NormalizedQuotient (M := surrealModelWith true)) =
    Category.canonicalDescClass (M := surrealModelWith true)
      (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModelWith true)) := by
  exact gate_canonicalDescClass_mk_eq_of_connected_generic
    (M := surrealModelWith true)
    (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))

theorem gate_rewrite_quotient_eq_add_zero_selectTrue
    (a : HExpr) :
    (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
      Category.NormalizedQuotient
        (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) =
    (Quot.mk _ a :
      Category.NormalizedQuotient
        (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) := by
  have hclass :
      Category.canonicalDescClass
        (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
        (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
          Category.NormalizedQuotient
            (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) =
      Category.canonicalDescClass
        (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
        (Quot.mk _ a :
          Category.NormalizedQuotient
            (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) := by
    exact gate_canonicalDescClass_mk_eq_of_connected_generic
      (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))
  exact gate_quotient_eq_of_canonicalDescClass_mk_eq_generic
    (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
    (h := hclass)

theorem gate_rewrite_canonicalDescClass_mk_eq_add_zero_selectTrue (a : HExpr) :
    Category.canonicalDescClass
      (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
        Category.NormalizedQuotient
          (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) =
    Category.canonicalDescClass
      (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (Quot.mk _ a :
        Category.NormalizedQuotient
          (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) := by
  exact gate_canonicalDescClass_mk_eq_of_connected_generic
    (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
    (h := gate_connected_of_rewrite1_generic (Category.HRewrite1.add_zero_right a))

theorem gate_add_zero_bundle_active (a : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
        (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) a ∧
    Category.NormalizedConnected
      (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (ExprC.add a (ExprC.C (0 : ℤ))) a ∧
    Category.canonicalDesc
      (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (ExprC.add a (ExprC.C (0 : ℤ))) =
      Category.canonicalDesc (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) a ∧
    Category.canonicalDescClass (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
      (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
        Category.NormalizedQuotient (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)) =
      Category.canonicalDescClass (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)
        (Quot.mk _ a :
          Category.NormalizedQuotient (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)) ∧
    (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
      Category.NormalizedQuotient (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)) =
      (Quot.mk _ a :
        Category.NormalizedQuotient (M := SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active)) := by
  refine ⟨gate_rewrite_eval_add_zero a, gate_rewrite_normalizedConnected_add_zero a,
    gate_rewrite_canonicalDesc_eq_add_zero a, gate_rewrite_canonicalDescClass_mk_eq_add_zero a,
    gate_rewrite_quotient_eq_add_zero a⟩

theorem gate_add_zero_bundle_surrealModel (a : HExpr) :
    HExpr.eval surrealModel (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval surrealModel a ∧
    Category.NormalizedConnected (M := surrealModel) (ExprC.add a (ExprC.C (0 : ℤ))) a ∧
    Category.canonicalDesc (M := surrealModel) (ExprC.add a (ExprC.C (0 : ℤ))) =
      Category.canonicalDesc (M := surrealModel) a ∧
    Category.canonicalDescClass (M := surrealModel)
      (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) : Category.NormalizedQuotient (M := surrealModel)) =
      Category.canonicalDescClass (M := surrealModel)
        (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModel)) ∧
    (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) : Category.NormalizedQuotient (M := surrealModel)) =
      (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModel)) := by
  refine ⟨gate_rewrite_eval_add_zero_surrealModel a, gate_rewrite_normalizedConnected_add_zero_surrealModel a,
    gate_rewrite_canonicalDesc_eq_add_zero_surrealModel a,
    gate_rewrite_canonicalDescClass_mk_eq_add_zero_surrealModel a,
    gate_rewrite_quotient_eq_add_zero_surrealModel a⟩

theorem gate_add_zero_bundle_selectTrue (a : HExpr) :
    HExpr.eval (SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
        (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval (SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) a ∧
    Category.NormalizedConnected
      (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (ExprC.add a (ExprC.C (0 : ℤ))) a ∧
    Category.canonicalDesc
      (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (ExprC.add a (ExprC.C (0 : ℤ))) =
      Category.canonicalDesc (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)) a ∧
    Category.canonicalDescClass
      (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
      (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
        Category.NormalizedQuotient
          (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) =
      Category.canonicalDescClass
        (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))
        (Quot.mk _ a :
          Category.NormalizedQuotient
            (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) ∧
    (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
      Category.NormalizedQuotient
        (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) =
      (Quot.mk _ a :
        Category.NormalizedQuotient
          (M := SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true))) := by
  refine ⟨gate_selectTrue_rewrite_eval_add_zero a, gate_selectTrue_rewrite_normalizedConnected_add_zero a,
    gate_selectTrue_rewrite_canonicalDesc_eq_add_zero a,
    gate_rewrite_canonicalDescClass_mk_eq_add_zero_selectTrue a,
    gate_rewrite_quotient_eq_add_zero_selectTrue a⟩

theorem gate_add_zero_bundle_modelWithTrue (a : HExpr) :
    HExpr.eval (surrealModelWith true) (ExprC.add a (ExprC.C (0 : ℤ))) =
      HExpr.eval (surrealModelWith true) a ∧
    Category.NormalizedConnected (M := surrealModelWith true)
      (ExprC.add a (ExprC.C (0 : ℤ))) a ∧
    Category.canonicalDesc (M := surrealModelWith true)
      (ExprC.add a (ExprC.C (0 : ℤ))) =
      Category.canonicalDesc (M := surrealModelWith true) a ∧
    Category.canonicalDescClass (M := surrealModelWith true)
      (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
        Category.NormalizedQuotient (M := surrealModelWith true)) =
      Category.canonicalDescClass (M := surrealModelWith true)
        (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModelWith true)) ∧
    (Quot.mk _ (ExprC.add a (ExprC.C (0 : ℤ))) :
      Category.NormalizedQuotient (M := surrealModelWith true)) =
      (Quot.mk _ a : Category.NormalizedQuotient (M := surrealModelWith true)) := by
  refine ⟨gate_rewrite_eval_add_zero_surrealModelWith_true a,
    gate_rewrite_normalizedConnected_add_zero_surrealModelWith_true a,
    gate_rewrite_canonicalDesc_eq_add_zero_surrealModelWith_true a,
    gate_rewrite_canonicalDescClass_mk_eq_add_zero_surrealModelWith_true a,
    gate_rewrite_quotient_eq_add_zero_surrealModelWith_true a⟩

end
end Hyperseries
end HeytingLean
