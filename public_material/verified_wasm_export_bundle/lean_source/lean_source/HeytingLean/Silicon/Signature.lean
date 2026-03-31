import HeytingLean.Probability.InfoTheory.FinDist

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

namespace Signature

variable {α : Type u} [Fintype α]

/-- If two finite distributions differ, then some point mass differs. -/
theorem exists_pmf_ne_of_ne (P Q : FinDist α) (h : P ≠ Q) : ∃ a : α, P.pmf a ≠ Q.pmf a := by
  classical
  by_contra hNo
  have hall : ∀ a : α, P.pmf a = Q.pmf a := by
    intro a
    by_contra hneq
    exact hNo ⟨a, hneq⟩
  exact h (FinDist.ext P Q hall)

variable [DecidableEq α]

/-- Probability of the singleton event `{a}` is exactly `P(a)`. -/
theorem probEvent_eq_pmf (P : FinDist α) (a : α) :
    FinDist.probEvent P (fun x : α => x = a) = P.pmf a := by
  classical
  rw [FinDist.probEvent_eq_sum (P := P) (E := fun x : α => x = a)]
  simp

/-- Distinct distributions are distinguishable by a singleton-event probability. -/
theorem exists_singleton_prob_ne (P Q : FinDist α) (h : P ≠ Q) :
    ∃ a : α,
      FinDist.probEvent P (fun x : α => x = a) ≠ FinDist.probEvent Q (fun x : α => x = a) := by
  classical
  rcases exists_pmf_ne_of_ne (α := α) P Q h with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [probEvent_eq_pmf (α := α) (P := P) (a := a), probEvent_eq_pmf (α := α) (P := Q) (a := a)] using ha

end Signature

end
end Silicon
end HeytingLean
