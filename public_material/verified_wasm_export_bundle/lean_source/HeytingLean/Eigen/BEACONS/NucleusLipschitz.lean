import Mathlib.Algebra.Order.Group.MinMax
import HeytingLean.Eigen.NucleusReLU
import HeytingLean.Eigen.NucleusThreshold

namespace HeytingLean
namespace Eigen
namespace BEACONS

theorem abs_relu_sub_le_abs_sub (x y : ℝ) :
    |relu x - relu y| ≤ |x - y| := by
  simpa [relu] using abs_max_sub_max_le_abs x y 0

theorem relu_lipschitz_constant_one (x y : ℝ) :
    |relu x - relu y| ≤ (1 : ℝ) * |x - y| := by
  simpa using abs_relu_sub_le_abs_sub x y

theorem abs_threshold_sub_le_abs_sub (a x y : ℝ) :
    |threshold x a - threshold y a| ≤ |x - y| := by
  simpa [threshold] using abs_max_sub_max_le_abs x y a

theorem threshold_lipschitz_constant_one (a x y : ℝ) :
    |threshold x a - threshold y a| ≤ (1 : ℝ) * |x - y| := by
  simpa using abs_threshold_sub_le_abs_sub a x y

theorem reluNucleus_lipschitz_pointwise (n : Nat) (v w : Fin n → ℝ) (i : Fin n) :
    |reluNucleus n v i - reluNucleus n w i| ≤ |v i - w i| := by
  simpa using abs_relu_sub_le_abs_sub (v i) (w i)

theorem thresholdNucleus_lipschitz_pointwise
    (n : Nat) (a v w : Fin n → ℝ) (i : Fin n) :
    |thresholdNucleus n a v i - thresholdNucleus n a w i| ≤ |v i - w i| := by
  simpa using abs_threshold_sub_le_abs_sub (a i) (v i) (w i)

end BEACONS
end Eigen
end HeytingLean
