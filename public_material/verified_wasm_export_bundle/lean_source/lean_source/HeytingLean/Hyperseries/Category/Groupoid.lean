import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import HeytingLean.Hyperseries.Category.RewriteQuiver

namespace HeytingLean
namespace Hyperseries
namespace Category

open CategoryTheory

/-- Free groupoid on the hyperseries one-step rewrite quiver. -/
abbrev HExprFreeGroupoid : Type _ :=
  Quiver.FreeGroupoid HExpr1Obj

instance : Groupoid HExprFreeGroupoid := by
  infer_instance

/-- Embed a hyperseries expression as an object in the free groupoid. -/
abbrev GObj (e : HExpr) : HExprFreeGroupoid :=
  (Quiver.FreeGroupoid.of HExpr1Obj).obj (HExpr1Obj.ofExpr e)

namespace HRewrite1

/-- View a one-step rewrite as a morphism in the free groupoid. -/
def toGroupoid {a b : HExpr} (h : HRewrite1 a b) : GObj a ⟶ GObj b :=
  (Quiver.FreeGroupoid.of HExpr1Obj).map
    (X := HExpr1Obj.ofExpr a) (Y := HExpr1Obj.ofExpr b) ⟨h⟩

theorem toGroupoid_eval_sound {K : Type*} [CommRing K] (M : HyperserialModel K)
    {a b : HExpr} (h : HRewrite1 a b) :
    HExpr.eval M a = HExpr.eval M b :=
  HRewrite1.eval_sound (M := M) h

end HRewrite1

namespace HRewriteSteps

private theorem exists_toGroupoid :
    {a b : HExpr} → HRewriteSteps a b → Nonempty (GObj a ⟶ GObj b)
  | _, _, h =>
      by
        induction h using Relation.ReflTransGen.trans_induction_on with
        | refl a =>
            exact ⟨𝟙 (GObj a)⟩
        | single h =>
            exact ⟨HRewrite1.toGroupoid h⟩
        | trans hab hbc ihab ihbc =>
            rcases ihab with ⟨f⟩
            rcases ihbc with ⟨g⟩
            exact ⟨f ≫ g⟩

/--
View a finite rewrite chain as a morphism in the free groupoid.
This is chosen noncomputably from the existence witness above because
`HRewriteSteps` is proposition-valued (`ReflTransGen`).
-/
noncomputable def toGroupoid {a b : HExpr} (h : HRewriteSteps a b) : GObj a ⟶ GObj b :=
  Classical.choice (exists_toGroupoid h)

theorem toGroupoid_eval_sound {K : Type*} [CommRing K] (M : HyperserialModel K)
    {a b : HExpr} (h : HRewriteSteps a b) :
    HExpr.eval M a = HExpr.eval M b :=
  HRewriteSteps.eval_sound (M := M) h

end HRewriteSteps

end Category
end Hyperseries
end HeytingLean
