import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Crypto.Quantum.Bell.Tsirelson.QuantumCorrelations

/-!
# Tsirelson bound (vector strategy model)

We prove the standard inequality:

`|S| ≤ 2 * sqrt 2`

for the CHSH quantity induced by a vector strategy of unit vectors.
-/

namespace HeytingLean
namespace Crypto
namespace Quantum
namespace Bell
namespace Tsirelson

open HeytingLean.Crypto.Quantum.Bell.CHSH

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace Real V]

namespace QuantumStrategy

variable (S : QuantumStrategy V)

theorem chsh_rewrite :
    chshQuantity S.toCorrelator =
      inner Real S.a0 (S.b0 + S.b1) + inner Real S.a1 (S.b0 - S.b1) := by
  simp [CHSH.chshQuantity, QuantumStrategy.toCorrelator, QuantumStrategy.aVec, QuantumStrategy.bVec,
    inner_add_right, inner_sub_right]
  ring

private theorem norm_sum_le_two_sqrt_two :
    norm (S.b0 + S.b1) + norm (S.b0 - S.b1) ≤ 2 * Real.sqrt 2 := by
  have hb0 : norm S.b0 = 1 := S.norm_b0
  have hb1 : norm S.b1 = 1 := S.norm_b1

  have hsumSq :
      norm (S.b0 + S.b1) ^ 2 + norm (S.b0 - S.b1) ^ 2 = (4 : Real) := by
    have hpar := parallelogram_law_with_norm (𝕜 := Real) S.b0 S.b1
    have hnorms : norm S.b0 ^ 2 + norm S.b1 ^ 2 = (2 : Real) := by
      simp [hb0, hb1]
      norm_num
    nlinarith [hpar, hnorms]

  have hnonneg : 0 ≤ norm (S.b0 + S.b1) + norm (S.b0 - S.b1) :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)

  have hsq : (norm (S.b0 + S.b1) + norm (S.b0 - S.b1)) ^ 2 ≤ (8 : Real) := by
    have hadd := add_sq_le (a := norm (S.b0 + S.b1)) (b := norm (S.b0 - S.b1))
    nlinarith [hadd, hsumSq]

  have hsqrt : norm (S.b0 + S.b1) + norm (S.b0 - S.b1) ≤ Real.sqrt 8 :=
    (Real.le_sqrt hnonneg (by norm_num)).2 hsq

  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    have h8 : (8 : Real) = 4 * 2 := by norm_num
    calc
      Real.sqrt 8 = Real.sqrt (4 * 2) := by simp [h8]
      _ = Real.sqrt 4 * Real.sqrt 2 := by
            simp [Real.sqrt_mul (x := (4 : Real)) (by norm_num) (2 : Real)]
      _ = 2 * Real.sqrt 2 := by
            have hsqrt4 : Real.sqrt (4 : Real) = 2 := by norm_num
            simp [hsqrt4]

  simpa [hsqrt8] using hsqrt

/-- Tsirelson bound for the CHSH quantity of a vector strategy. -/
theorem tsirelson_bound :
    |chshQuantity S.toCorrelator| ≤ 2 * Real.sqrt 2 := by
  have hrewrite := S.chsh_rewrite
  calc
    |chshQuantity S.toCorrelator| =
        |inner Real S.a0 (S.b0 + S.b1) + inner Real S.a1 (S.b0 - S.b1)| := by
          simp [hrewrite]
    _ ≤ |inner Real S.a0 (S.b0 + S.b1)| + |inner Real S.a1 (S.b0 - S.b1)| := by
          simpa using
            (abs_add_le (inner Real S.a0 (S.b0 + S.b1)) (inner Real S.a1 (S.b0 - S.b1)))
    _ ≤ norm S.a0 * norm (S.b0 + S.b1) + norm S.a1 * norm (S.b0 - S.b1) := by
          gcongr
          · exact abs_real_inner_le_norm S.a0 (S.b0 + S.b1)
          · exact abs_real_inner_le_norm S.a1 (S.b0 - S.b1)
    _ = norm (S.b0 + S.b1) + norm (S.b0 - S.b1) := by
          simp [S.norm_a0, S.norm_a1]
    _ ≤ 2 * Real.sqrt 2 := S.norm_sum_le_two_sqrt_two

end QuantumStrategy

end Tsirelson
end Bell
end Quantum
end Crypto
end HeytingLean

