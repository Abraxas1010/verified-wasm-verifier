import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import HeytingLean.Probability.InfoTheory.FinDist

namespace HeytingLean
namespace Epiplexity

open scoped BigOperators

/-- Bitstrings of fixed length `n`, represented as a finite type. -/
abbrev BitStr (n : Nat) := Fin (2 ^ n)

/-- Base-2 logarithm on reals. -/
noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

namespace FinDist

open HeytingLean.Probability.InfoTheory

variable {α : Type u} [Fintype α] [Nonempty α]

/-- Uniform distribution on a nonempty finite type, as a `FinDist`. -/
noncomputable def uniform : Probability.InfoTheory.FinDist α where
  pmf _ := 1 / (Fintype.card α : ℝ)
  nonneg _ := by
    have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := by
      exact_mod_cast Fintype.card_pos
    exact (one_div_nonneg.mpr (le_of_lt hcard))
  sum_one := by
    classical
    have hcard0 : (Fintype.card α : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Fintype.card_pos (α := α)))
    -- `∑ a, (1 / card) = card * (1 / card) = 1`.
    calc
      (∑ _a : α, (1 / (Fintype.card α : ℝ)))
          = (Fintype.card α : ℝ) * (1 / (Fintype.card α : ℝ)) := by
              simp [Finset.sum_const]
      _ = 1 := by
            simp [one_div, hcard0]

@[simp] theorem uniform_pmf (a : α) :
    (uniform : Probability.InfoTheory.FinDist α).pmf a = 1 / (Fintype.card α : ℝ) :=
  rfl

theorem uniform_Pos : (uniform : Probability.InfoTheory.FinDist α).Pos := by
  intro a
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  simpa [uniform_pmf] using (one_div_pos.mpr hcard)

end FinDist

end Epiplexity
end HeytingLean
