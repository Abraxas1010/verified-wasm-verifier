import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Eigen.BEACONS.MoCTransport

namespace HeytingLean
namespace Eigen
namespace BEACONS

/-!
PDE-level method-of-characteristics bridge for 1D linear advection:

  ∂ₜu + c ∂ₓu = 0

with transported profile `u(t,x) = u₀(x - c t)`.

This strengthens the earlier transport-level invariants by proving explicit
time/space derivative formulas and the exact PDE residual cancellation.
-/

noncomputable section

def transportTimeSlice (u0 : ℝ → ℝ) (c x : ℝ) : ℝ → ℝ :=
  fun t => transportSolution u0 c t x

def transportSpaceSlice (u0 : ℝ → ℝ) (c t : ℝ) : ℝ → ℝ :=
  fun x => transportSolution u0 c t x

theorem transportTimeSlice_hasDerivAt
    {u0 u0' : ℝ → ℝ}
    (hDeriv : ∀ z, HasDerivAt u0 (u0' z) z)
    (c t x : ℝ) :
    HasDerivAt (transportTimeSlice u0 c x)
      ((-c) * u0' (x - c * t)) t := by
  unfold transportTimeSlice transportSolution
  have hInner0 : HasDerivAt (fun τ : ℝ => x - c * τ) (0 - c) t := by
    convert (hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul c) using 1
    ring
  have hInner : HasDerivAt (fun τ : ℝ => x - c * τ) (-c) t := by
    simpa using hInner0
  have hOuter : HasDerivAt u0 (u0' (x - c * t)) (x - c * t) := hDeriv (x - c * t)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hOuter.comp t hInner

theorem transportSpaceSlice_hasDerivAt
    {u0 u0' : ℝ → ℝ}
    (hDeriv : ∀ z, HasDerivAt u0 (u0' z) z)
    (c t x : ℝ) :
    HasDerivAt (transportSpaceSlice u0 c t)
      (u0' (x - c * t)) x := by
  unfold transportSpaceSlice transportSolution
  have hInner0 : HasDerivAt (fun ξ : ℝ => ξ - c * t) (1 - 0) x := by
    change HasDerivAt ((fun ξ : ℝ => ξ) - (fun _ : ℝ => c * t)) (1 - 0) x
    exact (hasDerivAt_id x).sub (hasDerivAt_const x (c * t))
  have hInner : HasDerivAt (fun ξ : ℝ => ξ - c * t) 1 x := by
    simpa using hInner0
  have hOuter : HasDerivAt u0 (u0' (x - c * t)) (x - c * t) := hDeriv (x - c * t)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hOuter.comp x hInner

theorem transport_pde_residual_zero
    {u0 u0' : ℝ → ℝ}
    (hDeriv : ∀ z, HasDerivAt u0 (u0' z) z)
    (c t x : ℝ) :
    ∃ dt dx,
      HasDerivAt (transportTimeSlice u0 c x) dt t ∧
      HasDerivAt (transportSpaceSlice u0 c t) dx x ∧
      dt + c * dx = 0 := by
  refine ⟨(-c) * u0' (x - c * t), u0' (x - c * t), ?_, ?_, ?_⟩
  · exact transportTimeSlice_hasDerivAt hDeriv c t x
  · exact transportSpaceSlice_hasDerivAt hDeriv c t x
  · ring

theorem transport_pde_residual_zero_pointwise
    {u0' : ℝ → ℝ}
    (c t x : ℝ) :
    ((-c) * u0' (x - c * t)) + c * (u0' (x - c * t)) = 0 := by
  ring

end

end BEACONS
end Eigen
end HeytingLean
