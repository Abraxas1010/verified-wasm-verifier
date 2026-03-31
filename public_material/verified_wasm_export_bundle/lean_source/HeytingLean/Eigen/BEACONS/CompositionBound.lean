import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HeytingLean
namespace Eigen
namespace BEACONS

/-!
Lipschitz-specialized BEACONS composition bound in uniform (pointwise) form:

`|f (g x) - f̂ (ĝ x)| ≤ ε_f + L * ε_g`
-/

  theorem composition_error_bound
    {f fHat g gHat : ℝ → ℝ} {εf εg L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hOuterErr : ∀ x, |f x - fHat x| ≤ εf)
    (hOuterLip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hInnerErr : ∀ x, |g x - gHat x| ≤ εg) :
    ∀ x, |f (g x) - fHat (gHat x)| ≤ εf + L * εg := by
  intro x
  have hLip : |f (g x) - f (gHat x)| ≤ L * |g x - gHat x| := hOuterLip (g x) (gHat x)
  have hErr : |f (gHat x) - fHat (gHat x)| ≤ εf := hOuterErr (gHat x)
  have hMul : L * |g x - gHat x| ≤ L * εg :=
    mul_le_mul_of_nonneg_left (hInnerErr x) hL_nonneg
  calc
    |f (g x) - fHat (gHat x)|
        ≤ |f (g x) - f (gHat x)| + |f (gHat x) - fHat (gHat x)| := by
            exact abs_sub_le _ _ _
    _ ≤ (L * |g x - gHat x|) + εf := add_le_add hLip hErr
    _ ≤ (L * εg) + εf := add_le_add_right hMul εf
    _ = εf + L * εg := by ring

/-- Canonical theorem alias requested by the BEACONS integration track. -/
theorem latent_composition_error
    {f fHat g gHat : ℝ → ℝ} {εf εg L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hOuterErr : ∀ x, |f x - fHat x| ≤ εf)
    (hOuterLip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hInnerErr : ∀ x, |g x - gHat x| ≤ εg) :
    ∀ x, |f (g x) - fHat (gHat x)| ≤ εf + L * εg :=
  composition_error_bound hL_nonneg hOuterErr hOuterLip hInnerErr

end BEACONS
end Eigen
end HeytingLean
