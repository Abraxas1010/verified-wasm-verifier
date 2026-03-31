import Mathlib.CategoryTheory.Groupoid.Discrete
import HeytingLean.Hyperseries.Category.Groupoid
import HeytingLean.Hyperseries.Category.SemanticsAdapter
import HeytingLean.Hyperseries.Description

namespace HeytingLean
namespace Hyperseries
namespace Category

open CategoryTheory

section EvalLift

variable {K : Type*} [CommRing K] (M : HyperserialModel K)

/--
Prefunctor sending one-step hyperseries rewrites to equality morphisms
in the discrete groupoid on semantic values.
-/
def evalPrefunctor : HExpr1Obj ⥤q Discrete K where
  obj X := Discrete.mk (HExpr.eval M X.expr)
  map {_ _} h := Discrete.eqToHom (HRewrite1.eval_sound (M := M) h.down)

/--
Lift semantic evaluation from the one-step rewrite quiver to the
free groupoid on hyperseries expressions.
-/
noncomputable def evalLift : HExprFreeGroupoid ⥤ Discrete K :=
  Quiver.FreeGroupoid.lift (evalPrefunctor (M := M))

@[simp] theorem evalLift_obj (e : HExpr) :
    (evalLift (M := M)).obj (GObj e) = Discrete.mk (HExpr.eval M e) := by
  have hspec := Quiver.FreeGroupoid.lift_spec (φ := evalPrefunctor (M := M))
  have hobj := congrArg (fun F => F.obj (HExpr1Obj.ofExpr e)) hspec
  simpa [evalLift, GObj, evalPrefunctor] using hobj

/--
Any morphism in the hyperseries free-groupoid identifies expressions
with equal semantics in the chosen model.
-/
theorem eval_eq_of_groupoid_hom {a b : HExpr} (f : GObj a ⟶ GObj b) :
    HExpr.eval M a = HExpr.eval M b := by
  have h :
      ((evalLift (M := M)).obj (GObj a)).as = ((evalLift (M := M)).obj (GObj b)).as :=
    Discrete.eq_of_hom ((evalLift (M := M)).map f)
  simpa [evalLift_obj (M := M) a, evalLift_obj (M := M) b] using h

theorem eval_eq_of_connected {a b : HExpr} (h : Nonempty (GObj a ⟶ GObj b)) :
    HExpr.eval M a = HExpr.eval M b := by
  rcases h with ⟨f⟩
  exact eval_eq_of_groupoid_hom (M := M) f

theorem eval_eq_of_rewrite_steps {a b : HExpr} (h : HRewriteSteps a b) :
    HExpr.eval M a = HExpr.eval M b :=
  eval_eq_of_groupoid_hom (M := M) (HRewriteSteps.toGroupoid h)

end EvalLift

section Canonicalization

variable {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)

/-- Canonical description attached to a hyperseries expression in model `M`. -/
noncomputable def canonicalDesc (e : HExpr) : HDesc K :=
  HyperserialDescription.describe (K := K) (HExpr.eval M e)

/--
Staged normalized-quotient connectivity relation:
expressions are connected when their normalized forms share the same
canonical description.
-/
def NormalizedConnected (a b : HExpr) : Prop :=
  canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b)

theorem normalizedConnected_refl (a : HExpr) :
    NormalizedConnected (M := M) a a := by
  rfl

theorem normalizedConnected_symm {a b : HExpr}
    (h : NormalizedConnected (M := M) a b) :
    NormalizedConnected (M := M) b a := by
  exact h.symm

theorem normalizedConnected_trans {a b c : HExpr}
    (hab : NormalizedConnected (M := M) a b)
    (hbc : NormalizedConnected (M := M) b c) :
    NormalizedConnected (M := M) a c := by
  exact hab.trans hbc

def normalizedConnectedSetoid : Setoid HExpr where
  r := NormalizedConnected (M := M)
  iseqv := ⟨normalizedConnected_refl (M := M), normalizedConnected_symm (M := M),
    normalizedConnected_trans (M := M)⟩

/-- Quotient of hyperseries expressions by `NormalizedConnected`. -/
abbrev NormalizedQuotient (M : HyperserialModel K) : Sort _ :=
  Quotient (normalizedConnectedSetoid (M := M))

theorem quotient_eq_of_normalizedConnected {a b : HExpr}
    (h : NormalizedConnected (M := M) a b) :
    (Quot.mk _ a : NormalizedQuotient M) = (Quot.mk _ b : NormalizedQuotient M) :=
  Quotient.sound h

theorem normalizedConnected_of_quotient_eq {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient M) = (Quot.mk _ b : NormalizedQuotient M)) :
    NormalizedConnected (M := M) a b :=
  Quotient.exact h

theorem quotient_eq_iff_normalizedConnected (a b : HExpr) :
    ((Quot.mk _ a : NormalizedQuotient M) = (Quot.mk _ b : NormalizedQuotient M)) ↔
      NormalizedConnected (M := M) a b := by
  constructor
  · exact normalizedConnected_of_quotient_eq (M := M)
  · exact quotient_eq_of_normalizedConnected (M := M)

/--
Canonical description descends to the normalized-connectivity quotient.
-/
noncomputable def canonicalDescClass (q : NormalizedQuotient M) : HDesc K :=
  Quotient.lift (fun e => canonicalDesc (M := M) (nf e)) (by
    intro a b hab
    simpa [NormalizedConnected] using hab) q

@[simp] theorem canonicalDescClass_mk (a : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a) =
      canonicalDesc (M := M) (nf a) := rfl

theorem canonicalDescClass_eq_of_normalizedConnected {a b : HExpr}
    (h : NormalizedConnected (M := M) a b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M) := by
  simpa using congrArg (canonicalDescClass (M := M))
    (quotient_eq_of_normalizedConnected (M := M) h)

theorem canonicalDescClass_mk_eq_iff_normalizedConnected (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M) ↔
      NormalizedConnected (M := M) a b := by
  simp [canonicalDescClass_mk, NormalizedConnected]

theorem normalizedConnected_of_canonicalDescClass_mk_eq {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M)) :
    NormalizedConnected (M := M) a b :=
  (canonicalDescClass_mk_eq_iff_normalizedConnected (M := M) a b).1 h

theorem quotient_eq_of_canonicalDescClass_mk_eq {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M)) :
    (Quot.mk _ a : NormalizedQuotient M) = (Quot.mk _ b : NormalizedQuotient M) :=
  quotient_eq_of_normalizedConnected (M := M)
    (normalizedConnected_of_canonicalDescClass_mk_eq (M := M) h)

theorem canonicalDescClass_mk_eq_of_quotient_eq {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient M) = (Quot.mk _ b : NormalizedQuotient M)) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M) := by
  simpa using congrArg (canonicalDescClass (M := M)) h

theorem quotient_eq_iff_canonicalDescClass_mk_eq (a b : HExpr) :
    ((Quot.mk _ a : NormalizedQuotient M) = (Quot.mk _ b : NormalizedQuotient M)) ↔
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M) := by
  constructor
  · exact canonicalDescClass_mk_eq_of_quotient_eq (M := M)
  · exact quotient_eq_of_canonicalDescClass_mk_eq (M := M)

theorem canonicalDescClass_mk_eq_of_rewrite_steps {a b : HExpr}
    (h : HRewriteSteps a b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M) := by
  apply canonicalDescClass_eq_of_normalizedConnected (M := M)
  unfold NormalizedConnected canonicalDesc
  exact congrArg (HyperserialDescription.describe (K := K)) (nf_steps_sound (M := M) h)

theorem canonicalDescClass_mk_eq_of_groupoid_hom {a b : HExpr}
    (f : GObj a ⟶ GObj b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M) := by
  apply (canonicalDescClass_mk_eq_iff_normalizedConnected (M := M) a b).2
  unfold NormalizedConnected canonicalDesc
  apply congrArg (HyperserialDescription.describe (K := K))
  calc
    HExpr.eval M (nf a) = HExpr.eval M a := nf_sound (M := M) a
    _ = HExpr.eval M b := eval_eq_of_groupoid_hom (M := M) f
    _ = HExpr.eval M (nf b) := (nf_sound (M := M) b).symm

theorem canonicalDescClass_mk_eq_of_connected {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M) := by
  rcases h with ⟨f⟩
  exact canonicalDescClass_mk_eq_of_groupoid_hom (M := M) f

theorem rewrite_steps_implies_normalizedConnected {a b : HExpr} (h : HRewriteSteps a b) :
    NormalizedConnected (M := M) a b := by
  unfold NormalizedConnected canonicalDesc
  exact congrArg (HyperserialDescription.describe (K := K)) (nf_steps_sound (M := M) h)

theorem groupoid_hom_implies_canonicalDesc_eq {a b : HExpr} (f : GObj a ⟶ GObj b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  unfold canonicalDesc
  exact congrArg (HyperserialDescription.describe (K := K))
    (eval_eq_of_groupoid_hom (M := M) f)

theorem connected_implies_canonicalDesc_eq {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  rcases h with ⟨f⟩
  exact groupoid_hom_implies_canonicalDesc_eq (M := M) f

/--
Staged canonicalization bridge:
for the current conservative normalizer (`nf = id`), canonical descriptions
coincide exactly when expressions are connected in the normalized quotient layer.
-/
theorem canonicalDesc_eq_iff_normalizedConnected (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      NormalizedConnected (M := M) a b := by
  simp [NormalizedConnected, canonicalDesc, nf]

theorem quotient_eq_of_canonicalDesc_eq {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient M) = (Quot.mk _ b : NormalizedQuotient M) :=
  quotient_eq_of_normalizedConnected (M := M)
    ((canonicalDesc_eq_iff_normalizedConnected (M := M) a b).1 h)

theorem canonicalDesc_eq_of_quotient_eq {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient M) = (Quot.mk _ b : NormalizedQuotient M)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDesc_eq_iff_normalizedConnected (M := M) a b).2
    ((quotient_eq_iff_normalizedConnected (M := M) a b).1 h)

theorem canonicalDesc_eq_iff_quotient_eq (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient M) = (Quot.mk _ b : NormalizedQuotient M)) := by
  constructor
  · exact quotient_eq_of_canonicalDesc_eq (M := M)
  · exact canonicalDesc_eq_of_quotient_eq (M := M)

theorem canonicalDescClass_mk_eq_of_canonicalDesc_eq {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M) :=
  canonicalDescClass_mk_eq_of_quotient_eq (M := M)
    (quotient_eq_of_canonicalDesc_eq (M := M) h)

theorem canonicalDesc_eq_of_canonicalDescClass_mk_eq {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_quotient_eq (M := M)
    ((quotient_eq_iff_canonicalDescClass_mk_eq (M := M) a b).2 h)

theorem canonicalDescClass_mk_eq_iff_canonicalDesc_eq (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient M) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient M) ↔
      canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  constructor
  · exact canonicalDesc_eq_of_canonicalDescClass_mk_eq (M := M)
  · exact canonicalDescClass_mk_eq_of_canonicalDesc_eq (M := M)

end Canonicalization

end Category
end Hyperseries
end HeytingLean
