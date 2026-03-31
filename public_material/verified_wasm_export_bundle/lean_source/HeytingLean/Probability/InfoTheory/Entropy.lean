import Mathlib.Data.Fintype.BigOperators
import HeytingLean.Probability.InfoTheory.FinDist

namespace HeytingLean
namespace Probability
namespace InfoTheory

noncomputable section

open scoped BigOperators

namespace FinDist

variable {α : Type u} [Fintype α]

def entropy (P : FinDist α) : ℝ :=
  ∑ a : α, entropyTerm (P.pmf a)

theorem entropy_eq_neg_sum_mul_log_of_Pos (P : FinDist α) (hP : P.Pos) :
    entropy P = - (∑ a : α, P.pmf a * Real.log (P.pmf a)) := by
  classical
  unfold entropy
  have hterm :
      (∑ a : α, entropyTerm (P.pmf a))
        = ∑ a : α, (-(P.pmf a)) * Real.log (P.pmf a) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    have ha : 0 < P.pmf a := hP a
    have ha_not_le : ¬ P.pmf a ≤ 0 := not_le_of_gt ha
    simp [entropyTerm, ha_not_le, safeLog_of_pos ha]
  calc
    (∑ a : α, entropyTerm (P.pmf a))
        = ∑ a : α, (-(P.pmf a)) * Real.log (P.pmf a) := hterm
    _ = - (∑ a : α, P.pmf a * Real.log (P.pmf a)) := by
          simp [neg_mul, Finset.sum_neg_distrib]

end FinDist

end

end InfoTheory
end Probability
end HeytingLean
