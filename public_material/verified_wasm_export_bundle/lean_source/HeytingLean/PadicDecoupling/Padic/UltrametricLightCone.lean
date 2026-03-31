import HeytingLean.PadicDecoupling.Padic.Ultrametric

namespace HeytingLean.PadicDecoupling.Padic

open Set padicNorm

variable (p : ℕ) [Fact p.Prime]

def causalBall (center : ℚ) (r : ℚ) : Set ℚ :=
  {x | padicNorm p (x - center) ≤ r}

omit [Fact p.Prime] in
theorem mem_causalBall_iff {center r x : ℚ} :
    x ∈ causalBall p center r ↔ padicNorm p (x - center) ≤ r :=
  Iff.rfl

theorem causalBall_convex (center : ℚ) (r : ℚ) (_hr : 0 ≤ r)
    (x y : ℚ) (hx : x ∈ causalBall p center r) (hy : y ∈ causalBall p center r) :
    padicNorm p (x - y) ≤ r := by
  have hrewrite : x - y = (x - center) - (y - center) := centered_difference_eq center x y
  calc
    padicNorm p (x - y) = padicNorm p ((x - center) - (y - center)) := by rw [hrewrite]
    _ ≤ max (padicNorm p (x - center)) (padicNorm p (y - center)) :=
      centered_difference_le_max p center x y
    _ ≤ r := max_le hx hy

theorem isosceles_triangle (q r : ℚ) (hne : padicNorm p q ≠ padicNorm p r) :
    padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r) :=
  padicNorm.add_eq_max_of_ne hne

end HeytingLean.PadicDecoupling.Padic
