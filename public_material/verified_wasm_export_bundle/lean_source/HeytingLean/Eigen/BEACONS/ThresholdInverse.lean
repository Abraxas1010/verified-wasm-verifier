import HeytingLean.Eigen.NucleusThreshold

namespace HeytingLean
namespace Eigen
namespace BEACONS

/-!
Constructive inverse facts for the threshold map on the open ray `(a, ∞)`.

On this domain, `threshold x a = x`, so the local inverse is the identity.
-/

def thresholdInvOn (_a : ℝ) (x : ℝ) : ℝ := x

theorem threshold_eq_self_of_gt (a x : ℝ) (hx : a < x) :
    threshold x a = x := by
  exact max_eq_left (le_of_lt hx)

theorem thresholdInvOn_left_inverse_on_openRay
    (a x : ℝ) (hx : a < x) :
    thresholdInvOn a (threshold x a) = x := by
  simp [thresholdInvOn, threshold_eq_self_of_gt, hx]

theorem thresholdInvOn_right_inverse_on_openRay
    (a y : ℝ) (hy : a < y) :
    threshold (thresholdInvOn a y) a = y := by
  simp [thresholdInvOn, threshold_eq_self_of_gt, hy]

  theorem threshold_has_local_inverse_on_openRay (a x : ℝ) (hx : a < x) :
    ∃ y, a < y ∧ threshold y a = x := by
  refine ⟨x, hx, ?_⟩
  simp [threshold_eq_self_of_gt, hx]

theorem threshold_injective_on_openRay
    (a x y : ℝ) (hx : a < x) (hy : a < y)
    (hxy : threshold x a = threshold y a) : x = y := by
  simpa [threshold_eq_self_of_gt, hx, hy] using hxy

end BEACONS
end Eigen
end HeytingLean
