import HeytingLean.Hyperseries.Category.RewriteQuiver

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.Category

example (a b c : HExpr) :
    HRewrite1 (ExprC.add (ExprC.add a b) c) (ExprC.add a (ExprC.add b c)) :=
  HRewrite1.add_assoc a b c

example (a : HExpr) :
    HRewriteSteps (ExprC.add a (ExprC.C (0 : ℤ))) a :=
  HRewriteSteps.single (HRewrite1.add_zero_right a)

example (a : HExpr) :
    HRewriteSteps (ExprC.mul (ExprC.C (1 : ℤ)) a) a :=
  HRewriteSteps.single (HRewrite1.mul_one_left a)

example (M : HyperserialModel Int) (a : HExpr) :
    HExpr.eval M (ExprC.add a (ExprC.C (0 : ℤ))) = HExpr.eval M a :=
  HRewrite1.eval_sound (M := M) (HRewrite1.add_zero_right a)

example (M : HyperserialModel Int) (a b : HExpr)
    (h : HRewrite1 a b) :
    HExpr.eval M a = HExpr.eval M b :=
  HRewrite1.eval_sound (M := M) h

example (M : HyperserialModel Int) (a b : HExpr)
    (h : HRewriteSteps a b) :
    HExpr.eval M a = HExpr.eval M b :=
  HRewriteSteps.eval_sound (M := M) h

example (a b : HExpr) (h : HRewrite1 a b) :
    (HExpr1Obj.ofExpr a ⟶ HExpr1Obj.ofExpr b) :=
  ⟨h⟩

example (M : HyperserialModel Int) (a b : HExpr)
    (h : HExpr1Obj.ofExpr a ⟶ HExpr1Obj.ofExpr b) :
    HExpr.eval M a = HExpr.eval M b := by
  simpa using quiver_hom_eval_sound (M := M) h

end Numbers
end Tests
end HeytingLean
