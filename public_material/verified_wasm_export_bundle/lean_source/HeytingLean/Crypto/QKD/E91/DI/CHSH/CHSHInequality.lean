import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Crypto.QKD.E91.DI.CHSH.LocalHiddenVariable

/-!
# CHSH inequality for local hidden variables

We prove `|S| ≤ 2` for correlators induced by any finite LHV model.

Proof sketch (standard):
- For each hidden variable λ, the deterministic CHSH value is ±2.
- Averaging with a probability distribution preserves the bound by triangle inequality.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91
namespace DI
namespace CHSH

open scoped BigOperators

namespace LocalHiddenVariableModel

variable (M : LocalHiddenVariableModel)

/-- Deterministic CHSH value for a fixed hidden variable `l`. -/
def detCHSH (l : M.Λ) : ℝ :=
  let a0 := Outcome.sign (M.alice l false)
  let a1 := Outcome.sign (M.alice l true)
  let b0 := Outcome.sign (M.bob l false)
  let b1 := Outcome.sign (M.bob l true)
  a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1

theorem abs_detCHSH_le_two (l : M.Λ) : |M.detCHSH l| ≤ (2 : ℝ) := by
  -- With `b0,b1 ∈ {±1}`, either `b0 = b1` or `b0 = -b1`, and the expression collapses to ±2.
  classical
  unfold detCHSH
  cases ha0 : M.alice l false <;>
  cases ha1 : M.alice l true <;>
  cases hb0 : M.bob l false <;>
  cases hb1 : M.bob l true <;>
  · -- 16 cases, all reduce to `|2|` or `|-2|`.
    all_goals
      simp [Outcome.sign]
      norm_num

/-- CHSH inequality for an LHV model: `|S| ≤ 2`. -/
theorem chsh_inequality :
    |chshQuantity (M.toCorrelator)| ≤ (2 : ℝ) := by
  classical
  -- Expand `S` as an average of deterministic values.
  have hS :
      chshQuantity (M.toCorrelator) =
        Finset.univ.sum (fun l => M.pmf l * M.detCHSH l) := by
    -- `simp` expands CHSH into a linear combination of four correlators.
    -- The remaining goal is just linearity of `∑` over `+` and `-`.
    simp [chshQuantity, LocalHiddenVariableModel.toCorrelator, detCHSH, LocalHiddenVariableModel.value]
    -- Now the goal is linearity of `Finset.univ.sum`.
    let f00 : M.Λ → ℝ := fun l => M.pmf l * (Outcome.sign (M.alice l false) * Outcome.sign (M.bob l false))
    let f01 : M.Λ → ℝ := fun l => M.pmf l * (Outcome.sign (M.alice l false) * Outcome.sign (M.bob l true))
    let f10 : M.Λ → ℝ := fun l => M.pmf l * (Outcome.sign (M.alice l true) * Outcome.sign (M.bob l false))
    let f11 : M.Λ → ℝ := fun l => M.pmf l * (Outcome.sign (M.alice l true) * Outcome.sign (M.bob l true))
    have h01 :
        (Finset.univ.sum f00 + Finset.univ.sum f01) =
          Finset.univ.sum (fun l => f00 l + f01 l) := by
      simpa using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset M.Λ)) (f := f00) (g := f01)).symm
    have h23 :
        (Finset.univ.sum f10 - Finset.univ.sum f11) =
          Finset.univ.sum (fun l => f10 l - f11 l) := by
      exact
        (Finset.sum_sub_distrib (s := (Finset.univ : Finset M.Λ)) (f := f10) (g := f11)).symm
    have hadd :
        (Finset.univ.sum (fun l => f00 l + f01 l) + Finset.univ.sum (fun l => f10 l - f11 l)) =
          Finset.univ.sum (fun l => (f00 l + f01 l) + (f10 l - f11 l)) := by
      simpa using
        (Finset.sum_add_distrib (s := (Finset.univ : Finset M.Λ))
          (f := fun l => f00 l + f01 l) (g := fun l => f10 l - f11 l)).symm
    -- Put everything together.
    have hfold :
        (Finset.univ.sum f00 + Finset.univ.sum f01) + (Finset.univ.sum f10 - Finset.univ.sum f11) =
          Finset.univ.sum (fun l => f00 l + f01 l) + Finset.univ.sum (fun l => f10 l - f11 l) := by
      rw [h01, h23]
    calc
      (∑ x, M.pmf x * ((M.alice x false).sign * (M.bob x false).sign)) +
            (∑ x, M.pmf x * ((M.alice x false).sign * (M.bob x true).sign)) +
          (∑ x, M.pmf x * ((M.alice x true).sign * (M.bob x false).sign)) -
            (∑ x, M.pmf x * ((M.alice x true).sign * (M.bob x true).sign)) =
          Finset.univ.sum f00 + Finset.univ.sum f01 + (Finset.univ.sum f10 - Finset.univ.sum f11) := by
            classical
            simp [f00, f01, f10, f11, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (Finset.univ.sum f00 + Finset.univ.sum f01) + (Finset.univ.sum f10 - Finset.univ.sum f11) := by
            simp [add_assoc]
      _ = Finset.univ.sum (fun l => f00 l + f01 l) + Finset.univ.sum (fun l => f10 l - f11 l) := hfold
      _ = Finset.univ.sum (fun l => (f00 l + f01 l) + (f10 l - f11 l)) := hadd
      _ = Finset.univ.sum (fun l => f00 l + f01 l + (f10 l - f11 l)) := by
            classical
            simp [add_assoc]
      _ = Finset.univ.sum (fun l => M.pmf l * M.detCHSH l) := by
            classical
            simp [f00, f01, f10, f11, detCHSH, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            ring_nf
  -- Triangle inequality + `|detCHSH| ≤ 2` + `∑ pmf = 1`.
  calc
    |chshQuantity (M.toCorrelator)|
        = |Finset.univ.sum (fun l => M.pmf l * M.detCHSH l)| := by simp [hS]
    _ ≤ Finset.univ.sum (fun l => |M.pmf l * M.detCHSH l|) := by
          simpa using
            (Finset.abs_sum_le_sum_abs (f := fun l => M.pmf l * M.detCHSH l)
              (s := (Finset.univ : Finset M.Λ)))
    _ = Finset.univ.sum (fun l => M.pmf l * |M.detCHSH l|) := by
          simp [abs_mul, abs_of_nonneg, M.pmf_nonneg]
    _ ≤ Finset.univ.sum (fun l => M.pmf l * (2 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro l _
          have hdet : |M.detCHSH l| ≤ (2 : ℝ) := M.abs_detCHSH_le_two l
          exact mul_le_mul_of_nonneg_left hdet (M.pmf_nonneg l)
    _ = (Finset.univ.sum M.pmf) * (2 : ℝ) := by
          simpa using
            (Finset.sum_mul (s := (Finset.univ : Finset M.Λ)) (f := M.pmf) (a := (2 : ℝ))).symm
    _ = (2 : ℝ) := by simp [M.pmf_sum_one]

end LocalHiddenVariableModel

end CHSH
end DI
end E91
end QKD
end Crypto
end HeytingLean
