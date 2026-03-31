import Mathlib.Data.Real.Basic

namespace HeytingLean
namespace Eigen
namespace BEACONS

/-!
Method-of-characteristics proxy quantities used by runtime gating.

The proxy is intentionally lightweight: it captures a monotone hazard score
from a Jacobian norm and a positive regularization margin.
-/

noncomputable section

def smoothnessScale (jacobianNorm margin : ℝ) : ℝ :=
  jacobianNorm / (margin + 1)

def blowupHazard (jacobianNorm margin : ℝ) : ℝ :=
  smoothnessScale jacobianNorm margin

def transitionJacobianProxy (deltaNorm dt : ℝ) : ℝ :=
  deltaNorm / dt

def transitionHazard (deltaNorm dt margin : ℝ) : ℝ :=
  smoothnessScale (transitionJacobianProxy deltaNorm dt) margin

theorem smoothnessScale_nonneg
    {jacobianNorm margin : ℝ}
    (hJ : 0 ≤ jacobianNorm) (hM : 0 ≤ margin) :
    0 ≤ smoothnessScale jacobianNorm margin := by
  unfold smoothnessScale
  have hDen : 0 ≤ margin + 1 := by
    have hOne : (0 : ℝ) ≤ 1 := by norm_num
    exact add_nonneg hM hOne
  exact div_nonneg hJ hDen

theorem blowupHazard_nonneg
    {jacobianNorm margin : ℝ}
    (hJ : 0 ≤ jacobianNorm) (hM : 0 ≤ margin) :
    0 ≤ blowupHazard jacobianNorm margin :=
  smoothnessScale_nonneg hJ hM

theorem smoothnessScale_monotone_in_jacobian
    {j₁ j₂ margin : ℝ}
    (hj : j₁ ≤ j₂) (hM : 0 ≤ margin) :
    smoothnessScale j₁ margin ≤ smoothnessScale j₂ margin := by
  unfold smoothnessScale
  have hDen : 0 ≤ margin + 1 := by
    have hOne : (0 : ℝ) ≤ 1 := by norm_num
    exact add_nonneg hM hOne
  exact div_le_div_of_nonneg_right hj hDen

theorem smoothnessScale_zero_jacobian (margin : ℝ) :
    smoothnessScale 0 margin = 0 := by
  unfold smoothnessScale
  simp

theorem transitionJacobianProxy_nonneg
    {deltaNorm dt : ℝ}
    (hDelta : 0 ≤ deltaNorm) (hDt : 0 < dt) :
    0 ≤ transitionJacobianProxy deltaNorm dt := by
  unfold transitionJacobianProxy
  exact div_nonneg hDelta (le_of_lt hDt)

theorem transitionHazard_nonneg
    {deltaNorm dt margin : ℝ}
    (hDelta : 0 ≤ deltaNorm) (hDt : 0 < dt) (hM : 0 ≤ margin) :
    0 ≤ transitionHazard deltaNorm dt margin := by
  unfold transitionHazard
  exact smoothnessScale_nonneg (transitionJacobianProxy_nonneg hDelta hDt) hM

end
end BEACONS
end Eigen
end HeytingLean
