import HeytingLean.Hyperseries.Category.Groupoid

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.Category
open CategoryTheory

noncomputable section

example : CategoryTheory.Groupoid HExprFreeGroupoid := by
  infer_instance

example (e : HExpr) : (GObj e ⟶ GObj e) :=
  𝟙 (GObj e)

example (a b : HExpr) (h : HRewrite1 a b) : (GObj a ⟶ GObj b) :=
  HRewrite1.toGroupoid h

example (a b : HExpr) (h : HRewriteSteps a b) : (GObj a ⟶ GObj b) :=
  HRewriteSteps.toGroupoid h

example (M : HyperserialModel Int) (a b : HExpr) (h : HRewrite1 a b) :
    HExpr.eval M a = HExpr.eval M b :=
  HRewrite1.toGroupoid_eval_sound (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) (h : HRewriteSteps a b) :
    HExpr.eval M a = HExpr.eval M b :=
  HRewriteSteps.toGroupoid_eval_sound (M := M) h

end
end Numbers
end Tests
end HeytingLean
