import HeytingLean.Hyperseries.Category.SemanticsAdapter

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.Category

example (e : HExpr) : nf (nf e) = nf e := by
  simp [nf_idem]

example (M : HyperserialModel Int) (e : HExpr) :
    HExpr.eval M (nf e) = HExpr.eval M e := by
  simpa using nf_sound (M := M) e

example (e : HExpr) : RingFragment (nf e) := by
  exact nf_preserves_fragment (h := trivial)

example (e : HExpr) : HRewriteSteps e (nf e) := by
  exact nf_complete_fragment e

example (M : HyperserialModel Int) (a b : HExpr) (h : HRewrite1 a b) :
    HExpr.eval M (nf a) = HExpr.eval M (nf b) := by
  exact nf_step_sound (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) (h : HRewriteSteps a b) :
    HExpr.eval M (nf a) = HExpr.eval M (nf b) := by
  exact nf_steps_sound (M := M) h

end Numbers
end Tests
end HeytingLean
