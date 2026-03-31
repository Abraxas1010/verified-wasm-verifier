import HeytingLean.PadicDecoupling.Padic.Valuation

namespace HeytingLean.PadicDecoupling.Padic

open padicNorm

variable (p : ℕ) [Fact p.Prime]

theorem centered_difference_le_max (center x y : ℚ) :
    padicNorm p ((x - center) - (y - center)) ≤
      max (padicNorm p (x - center)) (padicNorm p (y - center)) := by
  simpa using (padicNorm.sub (p := p) (q := x - center) (r := y - center))

theorem centered_difference_eq (center x y : ℚ) :
    x - y = (x - center) - (y - center) := by
  ring

end HeytingLean.PadicDecoupling.Padic
