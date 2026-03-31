import Mathlib.Logic.Relation
import Mathlib.CategoryTheory.PathCategory.Basic
import HeytingLean.Hyperseries.Eval

namespace HeytingLean
namespace Hyperseries
namespace Category

/--
Wrapper object for the one-step hyperseries rewrite quiver.
-/
structure HExpr1Obj where
  expr : HExpr

namespace HExpr1Obj

def ofExpr (e : HExpr) : HExpr1Obj := ⟨e⟩

@[simp] theorem expr_ofExpr (e : HExpr) : (ofExpr e).expr = e := rfl

end HExpr1Obj

/--
Conservative one-step rewrite relation for the ring fragment of `HExpr`.
This intentionally excludes speculative exp/log rewrite rules at IG-0.
-/
inductive HRewrite1 : HExpr → HExpr → Prop where
  | add_assoc (a b c : HExpr) :
      HRewrite1 (ExprC.add (ExprC.add a b) c) (ExprC.add a (ExprC.add b c))
  | add_assoc_rev (a b c : HExpr) :
      HRewrite1 (ExprC.add a (ExprC.add b c)) (ExprC.add (ExprC.add a b) c)
  | add_comm (a b : HExpr) :
      HRewrite1 (ExprC.add a b) (ExprC.add b a)
  | add_zero_left (a : HExpr) :
      HRewrite1 (ExprC.add (ExprC.C (0 : ℤ)) a) a
  | add_zero_right (a : HExpr) :
      HRewrite1 (ExprC.add a (ExprC.C (0 : ℤ))) a
  | mul_assoc (a b c : HExpr) :
      HRewrite1 (ExprC.mul (ExprC.mul a b) c) (ExprC.mul a (ExprC.mul b c))
  | mul_assoc_rev (a b c : HExpr) :
      HRewrite1 (ExprC.mul a (ExprC.mul b c)) (ExprC.mul (ExprC.mul a b) c)
  | mul_comm (a b : HExpr) :
      HRewrite1 (ExprC.mul a b) (ExprC.mul b a)
  | mul_one_left (a : HExpr) :
      HRewrite1 (ExprC.mul (ExprC.C (1 : ℤ)) a) a
  | mul_one_right (a : HExpr) :
      HRewrite1 (ExprC.mul a (ExprC.C (1 : ℤ))) a
  | mul_zero_left (a : HExpr) :
      HRewrite1 (ExprC.mul (ExprC.C (0 : ℤ)) a) (ExprC.C (0 : ℤ))
  | mul_zero_right (a : HExpr) :
      HRewrite1 (ExprC.mul a (ExprC.C (0 : ℤ))) (ExprC.C (0 : ℤ))
  | neg_neg (a : HExpr) :
      HRewrite1 (ExprC.neg (ExprC.neg a)) a
  | congr_add_left {a a' b : HExpr} :
      HRewrite1 a a' → HRewrite1 (ExprC.add a b) (ExprC.add a' b)
  | congr_add_right {a b b' : HExpr} :
      HRewrite1 b b' → HRewrite1 (ExprC.add a b) (ExprC.add a b')
  | congr_mul_left {a a' b : HExpr} :
      HRewrite1 a a' → HRewrite1 (ExprC.mul a b) (ExprC.mul a' b)
  | congr_mul_right {a b b' : HExpr} :
      HRewrite1 b b' → HRewrite1 (ExprC.mul a b) (ExprC.mul a b')
  | congr_neg {a a' : HExpr} :
      HRewrite1 a a' → HRewrite1 (ExprC.neg a) (ExprC.neg a')

namespace HRewrite1

theorem eval_sound {K : Type*} [CommRing K] (M : HyperserialModel K) {a b : HExpr}
    (h : HRewrite1 a b) :
    HExpr.eval M a = HExpr.eval M b := by
  induction h with
  | add_assoc a b c =>
      simpa [HExpr.eval] using
        _root_.add_assoc (HExpr.eval (K := K) M a) (HExpr.eval (K := K) M b) (HExpr.eval (K := K) M c)
  | add_assoc_rev a b c =>
      simpa [HExpr.eval] using
        (_root_.add_assoc (HExpr.eval (K := K) M a)
          (HExpr.eval (K := K) M b) (HExpr.eval (K := K) M c)).symm
  | add_comm a b =>
      simpa [HExpr.eval] using _root_.add_comm (HExpr.eval (K := K) M a) (HExpr.eval (K := K) M b)
  | add_zero_left a =>
      simp [HExpr.eval]
  | add_zero_right a =>
      simp [HExpr.eval]
  | mul_assoc a b c =>
      simpa [HExpr.eval] using
        _root_.mul_assoc (HExpr.eval (K := K) M a) (HExpr.eval (K := K) M b) (HExpr.eval (K := K) M c)
  | mul_assoc_rev a b c =>
      simpa [HExpr.eval] using
        (_root_.mul_assoc (HExpr.eval (K := K) M a)
          (HExpr.eval (K := K) M b) (HExpr.eval (K := K) M c)).symm
  | mul_comm a b =>
      simpa [HExpr.eval] using _root_.mul_comm (HExpr.eval (K := K) M a) (HExpr.eval (K := K) M b)
  | mul_one_left a =>
      simp [HExpr.eval]
  | mul_one_right a =>
      simp [HExpr.eval]
  | mul_zero_left a =>
      simp [HExpr.eval]
  | mul_zero_right a =>
      simp [HExpr.eval]
  | neg_neg a =>
      simp [HExpr.eval]
  | congr_add_left h ih =>
      simp [HExpr.eval, ih]
  | congr_add_right h ih =>
      simp [HExpr.eval, ih]
  | congr_mul_left h ih =>
      simp [HExpr.eval, ih]
  | congr_mul_right h ih =>
      simp [HExpr.eval, ih]
  | congr_neg h ih =>
      simp [HExpr.eval, ih]

end HRewrite1

/-- Reflexive-transitive closure of one-step hyperseries rewrites. -/
abbrev HRewriteSteps : HExpr → HExpr → Prop :=
  Relation.ReflTransGen HRewrite1

namespace HRewriteSteps

theorem refl (a : HExpr) : HRewriteSteps a a :=
  Relation.ReflTransGen.refl

theorem single {a b : HExpr} (h : HRewrite1 a b) : HRewriteSteps a b :=
  Relation.ReflTransGen.single h

theorem trans {a b c : HExpr} (hab : HRewriteSteps a b) (hbc : HRewriteSteps b c) :
    HRewriteSteps a c :=
  Relation.ReflTransGen.trans hab hbc

theorem eval_sound {K : Type*} [CommRing K] (M : HyperserialModel K) {a b : HExpr}
    (h : HRewriteSteps a b) :
    HExpr.eval M a = HExpr.eval M b := by
  induction h with
  | refl =>
      rfl
  | tail hab hbc ih =>
      exact Eq.trans ih (HRewrite1.eval_sound (M := M) hbc)

end HRewriteSteps

instance : Quiver HExpr1Obj where
  Hom X Y := PLift (HRewrite1 X.expr Y.expr)

theorem quiver_hom_eval_sound {K : Type*} [CommRing K] (M : HyperserialModel K)
    {X Y : HExpr1Obj} (h : X ⟶ Y) :
    HExpr.eval M X.expr = HExpr.eval M Y.expr :=
  HRewrite1.eval_sound (M := M) h.down

end Category
end Hyperseries
end HeytingLean
