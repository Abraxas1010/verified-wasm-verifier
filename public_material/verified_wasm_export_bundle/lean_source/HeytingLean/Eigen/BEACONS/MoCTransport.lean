import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HeytingLean
namespace Eigen
namespace BEACONS

/-!
Method-of-characteristics formalization for the 1D linear advection equation

  ∂ₜu + c ∂ₓu = 0

with constant transport speed `c`.

This module provides an exact characteristic flow and transport pullback model:

* `charFlow c t x₀ = x₀ + c * t`
* `transportSolution u₀ c t x = u₀ (x - c * t)`

and proves core MoC invariants used by the BEACONS stack:

1. constancy along characteristics,
2. translation-invariance of uniform error bounds,
3. preservation of Lipschitz constants under transport pullback.
-/

noncomputable section

def charFlow (c t x0 : ℝ) : ℝ :=
  x0 + c * t

def transportSolution (u0 : ℝ → ℝ) (c t x : ℝ) : ℝ :=
  u0 (x - c * t)

theorem charFlow_zero (c x0 : ℝ) :
    charFlow c 0 x0 = x0 := by
  unfold charFlow
  ring

theorem charFlow_add_time (c t s x0 : ℝ) :
    charFlow c (t + s) x0 = charFlow c t (charFlow c s x0) := by
  unfold charFlow
  ring

theorem transport_on_characteristic (u0 : ℝ → ℝ) (c t x0 : ℝ) :
    transportSolution u0 c t (charFlow c t x0) = u0 x0 := by
  unfold transportSolution charFlow
  ring_nf

theorem transport_uniform_error_invariant
    {u0 v0 : ℝ → ℝ} {ε c : ℝ}
    (hε : ∀ x, |u0 x - v0 x| ≤ ε) :
    ∀ t x, |transportSolution u0 c t x - transportSolution v0 c t x| ≤ ε := by
  intro t x
  simpa [transportSolution] using hε (x - c * t)

theorem transport_lipschitz_invariant
    {u0 : ℝ → ℝ} {L c : ℝ}
    (hLip : ∀ x y, |u0 x - u0 y| ≤ L * |x - y|) :
    ∀ t x y,
      |transportSolution u0 c t x - transportSolution u0 c t y| ≤ L * |x - y| := by
  intro t x y
  have h := hLip (x - c * t) (y - c * t)
  calc
    |transportSolution u0 c t x - transportSolution u0 c t y|
        = |u0 (x - c * t) - u0 (y - c * t)| := by rfl
    _ ≤ L * |(x - c * t) - (y - c * t)| := h
    _ = L * |x - y| := by
          congr 1
          ring_nf

def linearProfile (a b : ℝ) : ℝ → ℝ :=
  fun x => a * x + b

theorem linearProfile_along_characteristic_const
    (a b c x0 : ℝ) :
    (fun t => transportSolution (linearProfile a b) c t (charFlow c t x0))
      = (fun _ => linearProfile a b x0) := by
  funext t
  unfold transportSolution charFlow linearProfile
  ring

end
end BEACONS
end Eigen
end HeytingLean
