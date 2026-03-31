import HeytingLean.PadicDecoupling.Padic.UltrametricLightCone

namespace HeytingLean.PadicDecoupling.Padic

open padicNorm

variable (p : ℕ) [Fact p.Prime]

abbrev PadicWalk := ℕ → ℚ

def position (walk : PadicWalk) : ℕ → ℚ
  | 0 => 0
  | n + 1 => position walk n + walk n

theorem walk_bounded (walk : PadicWalk) (r : ℚ) (hr : 0 ≤ r)
    (hsteps : ∀ n, padicNorm p (walk n) ≤ r) :
    ∀ n, padicNorm p (position walk n) ≤ r := by
  intro n
  induction n with
  | zero =>
      simpa [position] using (show padicNorm p 0 ≤ r by rw [padicNorm.zero]; exact hr)
  | succ n ih =>
      calc
        padicNorm p (position walk (n + 1))
            = padicNorm p (position walk n + walk n) := by simp [position]
        _ ≤ max (padicNorm p (position walk n)) (padicNorm p (walk n)) :=
          padicNorm.nonarchimedean
        _ ≤ r := max_le ih (hsteps n)

end HeytingLean.PadicDecoupling.Padic
