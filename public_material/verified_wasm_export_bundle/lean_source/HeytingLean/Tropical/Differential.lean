import HeytingLean.Tropical.ReLU

/-!
# Tropical.Differential

Small “piecewise-linear” facts about ReLU that are useful for connecting tropical structure
to differential combinators.

We deliberately avoid any global differentiability claim: ReLU is not differentiable at `0`.
-/

namespace HeytingLean.Tropical

/-- Subdifferential of ReLU at a point. -/
def relu_subdifferential (x : ℝ) : Set ℝ :=
  if 0 < x then {1}
  else if x < 0 then {0}
  else Set.Icc 0 1

/-- ReLU is piecewise linear with two pieces. -/
theorem relu_piecewise (x : ℝ) : relu x = if 0 ≤ x then x else 0 := by
  by_cases hx : 0 ≤ x
  · simp [relu, hx]
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hxle : x ≤ 0 := le_of_lt hxlt
    simp [relu, hx, max_eq_left hxle]

/-- On the strictly-positive region, the ReLU finite difference is exact. -/
theorem relu_diff_of_pos (x dx : ℝ) (hx : 0 < x) (hx' : 0 < x + dx) :
    relu (x + dx) - relu x = dx := by
  have hx0 : 0 ≤ x := le_of_lt hx
  have hx0' : 0 ≤ x + dx := le_of_lt hx'
  calc
    relu (x + dx) - relu x = (x + dx) - x := by
      simp [relu, max_eq_right hx0, max_eq_right hx0']
    _ = dx := by
      exact add_sub_cancel_left x dx

/-- On the strictly-negative region, the ReLU finite difference is zero. -/
theorem relu_diff_of_neg (x dx : ℝ) (hx : x < 0) (hx' : x + dx < 0) :
    relu (x + dx) - relu x = 0 := by
  have hx0 : x ≤ 0 := le_of_lt hx
  have hx0' : x + dx ≤ 0 := le_of_lt hx'
  simp [relu, max_eq_left hx0, max_eq_left hx0']

end HeytingLean.Tropical
