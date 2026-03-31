import HeytingLean.Analysis.RZ

namespace HeytingLean
namespace Tests
namespace Analysis

open HeytingLean.Analysis.RZ
open HeytingLean.Analysis.RZ.Interval
open HeytingLean.Analysis.RZ.ExactReal

/-!
# Sanity checks for `Analysis.RZ.ExactReal` (compile-time only)

These are compile-only checks to keep strict builds stable; runtime demos live in executables.
-/

noncomputable def x : ExactReal := ExactReal.ofRat (1 : ℚ)
noncomputable def y : ExactReal := ExactReal.ofRat (2 : ℚ)
noncomputable def z : ExactReal := ExactReal.add x y

example (n : Nat) : (z.approx n).width ≤ 1 / pow2 n :=
  z.width_bound n

example (n : Nat) : sample z n ∈ z.approx n :=
  sample_mem z n

example : |sample z 0 - sample z 10| ≤ (1 : ℚ) := by
  have h := abs_sub_sample_le z (m := 0) (n := 10) (Nat.zero_le 10)
  simpa [pow2] using h

example (n : Nat) : sample (ExactReal.ofRat (3 : ℚ)) n = (3 : ℚ) := by
  have hs : sample (ExactReal.ofRat (3 : ℚ)) n ∈ Interval.ofRat (3 : ℚ) := by
    simpa [ExactReal.sample, ExactReal.ofRat] using (sample_mem (ExactReal.ofRat (3 : ℚ)) n)
  exact (Interval.mem_ofRat (q := (3 : ℚ)) (x := sample (ExactReal.ofRat (3 : ℚ)) n)).1 hs

end Analysis
end Tests
end HeytingLean
