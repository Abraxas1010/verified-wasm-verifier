import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Crypto.Quantum.Bell.Tsirelson.TsirelsonBound

/-!
# Achievability of the Tsirelson bound (vector strategy)

We give an explicit strategy in `ℝ²` achieving `S = 2√2`.
-/

namespace HeytingLean
namespace Crypto
namespace Quantum
namespace Bell
namespace Tsirelson

open HeytingLean.Crypto.Quantum.Bell.CHSH

noncomputable section

abbrev V2 : Type := EuclideanSpace ℝ (Fin 2)

namespace Examples

private noncomputable def stdONB : OrthonormalBasis (Fin 2) ℝ V2 :=
  EuclideanSpace.basisFun (ι := Fin 2) ℝ

private noncomputable def b0 : V2 := stdONB 0
private noncomputable def b1 : V2 := stdONB 1

private def a0 : V2 := (1 / Real.sqrt 2) • (b0 + b1)
private def a1 : V2 := (1 / Real.sqrt 2) • (b0 - b1)

private theorem norm_a0 : ‖a0‖ = (1 : ℝ) := by
  have hb0 : ‖b0‖ = (1 : ℝ) := by simp [b0, stdONB]
  have hb1 : ‖b1‖ = (1 : ℝ) := by simp [b1, stdONB]
  have hinner : inner ℝ b0 b1 = 0 := by
    simpa [b0, b1, stdONB] using
      (OrthonormalBasis.inner_eq_zero (b := stdONB) (by decide : (0 : Fin 2) ≠ 1))
  have hsq : ‖b0 + b1‖ ^ 2 = (2 : ℝ) := by
    have := norm_add_sq_real b0 b1
    nlinarith [this, hb0, hb1, hinner]
  have hnorm : ‖b0 + b1‖ = Real.sqrt 2 := by
    have : Real.sqrt (‖b0 + b1‖ ^ 2) = Real.sqrt 2 := by simp [hsq]
    simpa [Real.sqrt_sq (norm_nonneg (b0 + b1))] using this
  have hs : ‖(1 / Real.sqrt 2 : ℝ)‖ = (1 / Real.sqrt 2 : ℝ) := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hpos' : (0 : ℝ) < (1 / Real.sqrt 2 : ℝ) := one_div_pos.2 hpos
    have hnonneg : (0 : ℝ) ≤ (1 / Real.sqrt 2 : ℝ) := le_of_lt hpos'
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg hnonneg
  calc
    ‖a0‖ = ‖(1 / Real.sqrt 2 : ℝ)‖ * ‖b0 + b1‖ := by
      rw [a0]
      simpa using (norm_smul (1 / Real.sqrt 2 : ℝ) (b0 + b1))
    _ = (1 / Real.sqrt 2 : ℝ) * Real.sqrt 2 := by
      rw [hs, hnorm]
    _ = (1 : ℝ) := by
      have hpos : (Real.sqrt 2 : ℝ) ≠ 0 :=
        (Real.sqrt_ne_zero').2 (by norm_num)
      field_simp [hpos]

private theorem norm_a1 : ‖a1‖ = (1 : ℝ) := by
  have hb0 : ‖b0‖ = (1 : ℝ) := by simp [b0, stdONB]
  have hb1 : ‖b1‖ = (1 : ℝ) := by simp [b1, stdONB]
  have hinner : inner ℝ b0 b1 = 0 := by
    simpa [b0, b1, stdONB] using
      (OrthonormalBasis.inner_eq_zero (b := stdONB) (by decide : (0 : Fin 2) ≠ 1))
  have hsq : ‖b0 - b1‖ ^ 2 = (2 : ℝ) := by
    have := norm_sub_sq_real b0 b1
    nlinarith [this, hb0, hb1, hinner]
  have hnorm : ‖b0 - b1‖ = Real.sqrt 2 := by
    have : Real.sqrt (‖b0 - b1‖ ^ 2) = Real.sqrt 2 := by simp [hsq]
    simpa [Real.sqrt_sq (norm_nonneg (b0 - b1))] using this
  have hs : ‖(1 / Real.sqrt 2 : ℝ)‖ = (1 / Real.sqrt 2 : ℝ) := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hpos' : (0 : ℝ) < (1 / Real.sqrt 2 : ℝ) := one_div_pos.2 hpos
    have hnonneg : (0 : ℝ) ≤ (1 / Real.sqrt 2 : ℝ) := le_of_lt hpos'
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg hnonneg
  calc
    ‖a1‖ = ‖(1 / Real.sqrt 2 : ℝ)‖ * ‖b0 - b1‖ := by
      rw [a1]
      simpa using (norm_smul (1 / Real.sqrt 2 : ℝ) (b0 - b1))
    _ = (1 / Real.sqrt 2 : ℝ) * Real.sqrt 2 := by
      rw [hs, hnorm]
    _ = (1 : ℝ) := by
      have hpos : (Real.sqrt 2 : ℝ) ≠ 0 :=
        (Real.sqrt_ne_zero').2 (by norm_num)
      field_simp [hpos]

/-- An explicit strategy achieving `S = 2√2`. -/
def tsirelsonAchievingStrategy : QuantumStrategy V2 where
  a0 := a0
  a1 := a1
  b0 := b0
  b1 := b1
  norm_a0 := norm_a0
  norm_a1 := norm_a1
  norm_b0 := by simp [b0, stdONB]
  norm_b1 := by simp [b1, stdONB]

theorem achieves_tsirelson :
    chshQuantity (tsirelsonAchievingStrategy.toCorrelator) = 2 * Real.sqrt 2 := by
  classical
  have hrewrite := QuantumStrategy.chsh_rewrite (S := tsirelsonAchievingStrategy)

  have hb0 : ‖b0‖ = (1 : ℝ) := by simp [b0, stdONB]
  have hb1 : ‖b1‖ = (1 : ℝ) := by simp [b1, stdONB]
  have hinner : inner ℝ b0 b1 = 0 := by
    simpa [b0, b1, stdONB] using
      (OrthonormalBasis.inner_eq_zero (b := stdONB) (by decide : (0 : Fin 2) ≠ 1))

  have hsq_add : ‖b0 + b1‖ ^ 2 = (2 : ℝ) := by
    have h := norm_add_sq_real b0 b1
    nlinarith [h, hb0, hb1, hinner]
  have hsq_sub : ‖b0 - b1‖ ^ 2 = (2 : ℝ) := by
    have h := norm_sub_sq_real b0 b1
    nlinarith [h, hb0, hb1, hinner]

  have hsqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 :=
    (Real.sqrt_ne_zero').2 (by norm_num)

  have hterm1 : inner ℝ a0 (b0 + b1) = Real.sqrt 2 := by
    have hinner_self : inner ℝ (b0 + b1) (b0 + b1) = (2 : ℝ) := by
      calc
        inner ℝ (b0 + b1) (b0 + b1) = ‖b0 + b1‖ ^ 2 := by
          simpa using (real_inner_self_eq_norm_sq (b0 + b1))
        _ = (2 : ℝ) := by simp [hsq_add]
    calc
      inner ℝ a0 (b0 + b1) = (1 / Real.sqrt 2 : ℝ) * inner ℝ (b0 + b1) (b0 + b1) := by
        rw [a0]
        simpa using
          (inner_smul_left (𝕜 := ℝ) (b0 + b1) (b0 + b1) (1 / Real.sqrt 2 : ℝ))
      _ = (1 / Real.sqrt 2 : ℝ) * (2 : ℝ) := by simp [hinner_self]
      _ = Real.sqrt 2 := by
        field_simp [hsqrt2_ne]
        exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))).symm

  have hterm2 : inner ℝ a1 (b0 - b1) = Real.sqrt 2 := by
    have hinner_self : inner ℝ (b0 - b1) (b0 - b1) = (2 : ℝ) := by
      calc
        inner ℝ (b0 - b1) (b0 - b1) = ‖b0 - b1‖ ^ 2 := by
          simpa using (real_inner_self_eq_norm_sq (b0 - b1))
        _ = (2 : ℝ) := by simp [hsq_sub]
    calc
      inner ℝ a1 (b0 - b1) = (1 / Real.sqrt 2 : ℝ) * inner ℝ (b0 - b1) (b0 - b1) := by
        simp [a1, inner_smul_left]
      _ = (1 / Real.sqrt 2 : ℝ) * (2 : ℝ) := by simp [hinner_self]
      _ = Real.sqrt 2 := by
        field_simp [hsqrt2_ne]
        exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))).symm

  have hterm1' :
      inner ℝ tsirelsonAchievingStrategy.a0
          (tsirelsonAchievingStrategy.b0 + tsirelsonAchievingStrategy.b1) =
        Real.sqrt 2 := by
    simpa [tsirelsonAchievingStrategy] using hterm1
  have hterm2' :
      inner ℝ tsirelsonAchievingStrategy.a1
          (tsirelsonAchievingStrategy.b0 - tsirelsonAchievingStrategy.b1) =
        Real.sqrt 2 := by
    simpa [tsirelsonAchievingStrategy] using hterm2

  have hsum : chshQuantity (tsirelsonAchievingStrategy.toCorrelator) = Real.sqrt 2 + Real.sqrt 2 := by
    calc
      chshQuantity (tsirelsonAchievingStrategy.toCorrelator) =
          inner ℝ tsirelsonAchievingStrategy.a0
              (tsirelsonAchievingStrategy.b0 + tsirelsonAchievingStrategy.b1) +
            inner ℝ tsirelsonAchievingStrategy.a1
              (tsirelsonAchievingStrategy.b0 - tsirelsonAchievingStrategy.b1) := by
            simp [hrewrite]
      _ = Real.sqrt 2 + Real.sqrt 2 := by simp [hterm1', hterm2']

  simpa [two_mul, add_assoc, add_comm, add_left_comm] using hsum

end Examples

end

end Tsirelson
end Bell
end Quantum
end Crypto
end HeytingLean

