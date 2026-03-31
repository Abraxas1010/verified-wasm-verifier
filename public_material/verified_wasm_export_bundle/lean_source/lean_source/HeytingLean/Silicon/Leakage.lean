import Mathlib.Algebra.BigOperators.Ring.Finset
import HeytingLean.Probability.InfoTheory.MutualInfo
import HeytingLean.Silicon.Model

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

namespace FinDistLemmas

variable {α β : Type u} [Fintype α] [Fintype β]

/-- The left marginal of a product distribution is the left factor. -/
@[simp] theorem marginalLeft_prod (P : FinDist α) (Q : FinDist β) :
    FinDist.marginalLeft (α := α) (β := β) (FinDist.prod P Q) = P := by
  classical
  ext a
  calc
    (FinDist.marginalLeft (α := α) (β := β) (FinDist.prod P Q)).pmf a
        = ∑ b : β, P.pmf a * Q.pmf b := by
            simp [FinDist.marginalLeft, FinDist.prod]
    _ = P.pmf a * (∑ b : β, Q.pmf b) := by
            -- `∑ b, P(a) * Q(b) = P(a) * ∑ b, Q(b)`.
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset β)) (f := fun b : β => Q.pmf b)
                (a := P.pmf a)).symm
    _ = P.pmf a := by
            simp [Q.sum_one]

/-- The right marginal of a product distribution is the right factor. -/
@[simp] theorem marginalRight_prod (P : FinDist α) (Q : FinDist β) :
    FinDist.marginalRight (α := α) (β := β) (FinDist.prod P Q) = Q := by
  classical
  ext b
  calc
    (FinDist.marginalRight (α := α) (β := β) (FinDist.prod P Q)).pmf b
        = ∑ a : α, P.pmf a * Q.pmf b := by
            simp [FinDist.marginalRight, FinDist.prod]
    _ = (∑ a : α, P.pmf a) * Q.pmf b := by
            -- `∑ a, P(a) * Q(b) = (∑ a, P(a)) * Q(b)`.
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset α)) (f := fun a : α => P.pmf a)
                (a := Q.pmf b)).symm
    _ = Q.pmf b := by
            simp [P.sum_one]

end FinDistLemmas

variable {S O : Type u} [Fintype S] [Fintype O]

/-- Leakage of a run `P_{S,O}`: mutual information `I(S;O)` in nats. -/
abbrev Leakage (P : Run S O) : ℝ :=
  FinDist.mutualInfo (α := S) (β := O) P

/-- The product of marginals `P_S × P_O` (i.e. correlation erased). -/
def prodMarginals (P : Run S O) : Run S O :=
  FinDist.prod (Run.stateMarginal (S := S) (O := O) P) (Run.obsMarginal (S := S) (O := O) P)

/-- Independence (finite/discrete): a joint distribution is a product distribution. -/
def Independent (P : Run S O) : Prop :=
  ∃ (PS : FinDist S) (PO : FinDist O), P = FinDist.prod PS PO

theorem leakage_nonneg_of_prodMarginals_Pos (P : Run S O) (hprod : (prodMarginals (S := S) (O := O) P).Pos) :
    0 ≤ Leakage (S := S) (O := O) P := by
  simpa [Leakage, prodMarginals, Run.stateMarginal, Run.obsMarginal] using
    (FinDist.mutualInfo_nonneg_of_Pos (α := S) (β := O) P hprod)

theorem leakage_prodMarginals_zero (P : Run S O) :
    Leakage (S := S) (O := O) (prodMarginals (S := S) (O := O) P) = 0 := by
  classical
  -- Let `P0 := P_S × P_O`. Its marginals are exactly `P_S` and `P_O`, so `I(S;O)=0`.
  let PS : FinDist S := Run.stateMarginal (S := S) (O := O) P
  let PO : FinDist O := Run.obsMarginal (S := S) (O := O) P
  have hL :
      FinDist.marginalLeft (α := S) (β := O) (FinDist.prod PS PO) = PS :=
    FinDistLemmas.marginalLeft_prod (α := S) (β := O) PS PO
  have hR :
      FinDist.marginalRight (α := S) (β := O) (FinDist.prod PS PO) = PO :=
    FinDistLemmas.marginalRight_prod (α := S) (β := O) PS PO
  -- Unfold mutual information, rewrite marginals of `prod`, then reduce to `klDiv_self_zero`.
  simp [Leakage, prodMarginals, PS, PO, FinDist.mutualInfo, hL, hR]

theorem leakage_eq_zero_of_independent (P : Run S O) (h : Independent (S := S) (O := O) P) :
    Leakage (S := S) (O := O) P = 0 := by
  classical
  rcases h with ⟨PS, PO, rfl⟩
  have hL :
      FinDist.marginalLeft (α := S) (β := O) (FinDist.prod PS PO) = PS :=
    FinDistLemmas.marginalLeft_prod (α := S) (β := O) PS PO
  have hR :
      FinDist.marginalRight (α := S) (β := O) (FinDist.prod PS PO) = PO :=
    FinDistLemmas.marginalRight_prod (α := S) (β := O) PS PO
  simp [Leakage, FinDist.mutualInfo, hL, hR]

end
end Silicon
end HeytingLean
