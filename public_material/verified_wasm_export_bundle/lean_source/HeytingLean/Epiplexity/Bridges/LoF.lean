import HeytingLean.LoF.Nucleus
import HeytingLean.Probability.InfoTheory.FinDist

namespace HeytingLean
namespace Epiplexity
namespace Bridges
namespace LoF

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

noncomputable section

variable {α : Type u} [Fintype α] [HeytingLean.LoF.PrimaryAlgebra α]

/-- Pushforward of a finite distribution along a LoF re-entry nucleus. -/
noncomputable def closedDist (R : HeytingLean.LoF.Reentry α) (X : FinDist α) : FinDist α :=
  FinDist.map R X

/--
Closing a distribution under re-entry is idempotent: pushing forward twice along the nucleus is
the same as pushing forward once.
-/
theorem closedDist_idempotent (R : HeytingLean.LoF.Reentry α) (X : FinDist α) :
    closedDist R (closedDist R X) = closedDist R X := by
  classical
  ext b
  unfold closedDist
  simp [FinDist.map]
  have h1 :
      (∑ a : α, if R a = b then (∑ x : α, if R x = a then X.pmf x else 0) else 0)
        =
      ∑ a : α, ∑ x : α, if R a = b then if R x = a then X.pmf x else 0 else 0 := by
    refine Fintype.sum_congr _ _ (fun a => ?_)
    by_cases h : R a = b <;> simp [h]
  have hswap :
      (∑ a : α, ∑ x : α, if R a = b then if R x = a then X.pmf x else 0 else 0)
        =
      ∑ x : α, ∑ a : α, if R a = b then if R x = a then X.pmf x else 0 else 0 := by
    have h1' :
        (∑ ax : α × α, if R ax.1 = b then if R ax.2 = ax.1 then X.pmf ax.2 else 0 else 0)
          =
        ∑ a : α, ∑ x : α, if R a = b then if R x = a then X.pmf x else 0 else 0 := by
      simpa using
        (Fintype.sum_prod_type
          (fun ax : α × α =>
            if R ax.1 = b then if R ax.2 = ax.1 then X.pmf ax.2 else 0 else 0))
    have h2 :
        (∑ ax : α × α, if R ax.1 = b then if R ax.2 = ax.1 then X.pmf ax.2 else 0 else 0)
          =
        ∑ x : α, ∑ a : α, if R a = b then if R x = a then X.pmf x else 0 else 0 := by
      simpa using
        (Fintype.sum_prod_type_right
          (fun ax : α × α =>
            if R ax.1 = b then if R ax.2 = ax.1 then X.pmf ax.2 else 0 else 0))
    exact h1'.symm.trans h2
  calc
    (∑ a : α, if R a = b then (∑ x : α, if R x = a then X.pmf x else 0) else 0)
        =
      ∑ a : α, ∑ x : α, if R a = b then if R x = a then X.pmf x else 0 else 0 := h1
    _ =
      ∑ x : α, ∑ a : α, if R a = b then if R x = a then X.pmf x else 0 else 0 := hswap
    _ =
      ∑ x : α, if R (R x) = b then X.pmf x else 0 := by
        refine Fintype.sum_congr _ _ (fun x => ?_)
        calc
          (∑ a : α, if R a = b then if R x = a then X.pmf x else 0 else 0)
              =
            ∑ a : α, if R x = a then if R a = b then X.pmf x else 0 else 0 := by
              refine Fintype.sum_congr _ _ (fun a => ?_)
              by_cases hxa : R x = a <;> simp [hxa]
          _ = if R (R x) = b then X.pmf x else 0 := by
              simp
    _ = ∑ x : α, if R x = b then X.pmf x else 0 := by
        refine Fintype.sum_congr _ _ (fun x => by simp)

end
end LoF
end Bridges
end Epiplexity
end HeytingLean
