import Mathlib.Tactic
import HeytingLean.Probability.InfoTheory.FinDist
import HeytingLean.Silicon.Model

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

namespace Empirical

variable {ι α : Type u} [Fintype ι] [Fintype α]

/-- Uniform distribution on a nonempty finite type. -/
def uniform (ι : Type u) [Fintype ι] [Nonempty ι] : FinDist ι where
  pmf _ := 1 / (Fintype.card ι : ℝ)
  nonneg _ := by
    have hcard : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos
    exact one_div_nonneg.mpr (le_of_lt hcard)
  sum_one := by
    classical
    have hcard0 : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos (α := ι)))
    calc
      (∑ _i : ι, (1 / (Fintype.card ι : ℝ)))
          = (Fintype.card ι : ℝ) * (1 / (Fintype.card ι : ℝ)) := by
              simp [Finset.sum_const]
      _ = 1 := by
            field_simp [hcard0]

/-- Empirical distribution of a finite sample `f : ι → α` under a uniform choice of index `ι`. -/
noncomputable def empirical (ι α : Type u) [Fintype ι] [Nonempty ι] [Fintype α]
    (f : ι → α) : FinDist α :=
  FinDist.map f (uniform ι)

variable {S O : Type u} [Fintype S] [Fintype O]

/-- Empirical joint distribution `P_{S,O}` from samples indexed by `ι`. -/
noncomputable abbrev empiricalRun (ι : Type u) [Fintype ι] [Nonempty ι]
    (f : ι → (S × O)) : Run S O :=
  empirical (ι := ι) (α := (S × O)) f

end Empirical

end

end Silicon
end HeytingLean
