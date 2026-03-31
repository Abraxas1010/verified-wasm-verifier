import HeytingLean.Hyperseries.Category.RewriteQuiver

namespace HeytingLean
namespace Hyperseries
namespace Category

/--
Conservative fragment marker used for staged semantic adapter theorems.
IG-2.5 keeps this broad while the normalizer is intentionally minimal.
-/
def RingFragment (_e : HExpr) : Prop := True

/--
Staged normalizer candidate for the conservative fragment.
At IG-2.5 this is identity to guarantee semantic soundness while
the richer rewrite normalizer is developed.
-/
def nf (e : HExpr) : HExpr := e

@[simp] theorem nf_idem (e : HExpr) : nf (nf e) = nf e := rfl

theorem nf_sound {K : Type*} [CommRing K] (M : HyperserialModel K) (e : HExpr) :
    HExpr.eval M (nf e) = HExpr.eval M e := rfl

theorem nf_preserves_fragment {e : HExpr} (h : RingFragment e) : RingFragment (nf e) := h

/--
Fragment completeness witness for IG-2.5:
each expression rewrites to its staged normal form in zero steps.
-/
theorem nf_complete_fragment (e : HExpr) : HRewriteSteps e (nf e) :=
  HRewriteSteps.refl e

theorem nf_step_sound {K : Type*} [CommRing K] (M : HyperserialModel K) {a b : HExpr}
    (h : HRewrite1 a b) :
    HExpr.eval M (nf a) = HExpr.eval M (nf b) := by
  simpa [nf] using HRewrite1.eval_sound (M := M) h

theorem nf_steps_sound {K : Type*} [CommRing K] (M : HyperserialModel K) {a b : HExpr}
    (h : HRewriteSteps a b) :
    HExpr.eval M (nf a) = HExpr.eval M (nf b) := by
  simpa [nf] using HRewriteSteps.eval_sound (M := M) h

end Category
end Hyperseries
end HeytingLean
