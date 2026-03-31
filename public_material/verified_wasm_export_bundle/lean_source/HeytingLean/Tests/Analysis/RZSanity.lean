import HeytingLean.Analysis.RZ

namespace HeytingLean
namespace Tests
namespace Analysis

open HeytingLean.Analysis.RZ
open HeytingLean.Analysis.RZ.Interval

/-!
# Sanity checks for `Analysis.RZ` (compile-time only)

These are compile-only checks to keep strict builds stable; runtime demos live in executables.
-/

example (p : Nat) (q : ℚ) : roundDown p q ≤ roundUp p q :=
  roundDown_le_roundUp p q

noncomputable def I01 : Interval := Interval.make (0 : ℚ) 1
noncomputable def I12 : Interval := Interval.make (1 : ℚ) 2

example : (1 : ℚ) ∈ I01 := by
  simp [I01, Interval.make]

example : (1 : ℚ) + (2 : ℚ) ∈ Interval.add 4 (Interval.ofRat (1 : ℚ)) (Interval.ofRat (2 : ℚ)) := by
  have hx : (1 : ℚ) ∈ Interval.ofRat (1 : ℚ) := by
    simp [Interval.ofRat]
  have hy : (2 : ℚ) ∈ Interval.ofRat (2 : ℚ) := by
    simp [Interval.ofRat]
  simpa using (Interval.mem_add (p := 4) (I := Interval.ofRat (1 : ℚ)) (J := Interval.ofRat (2 : ℚ)) hx hy)

end Analysis
end Tests
end HeytingLean
