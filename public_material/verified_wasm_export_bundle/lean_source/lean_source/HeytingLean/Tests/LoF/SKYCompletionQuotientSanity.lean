import HeytingLean.LoF.Combinators.Category.CompletionQuotient

/-!
# Smoke test: completion quotient category

This file checks that a concrete completion cell collapses its two boundary paths in the
completion-quotient path category.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

private def left : Comb := Comb.app (Comb.app .K .S) .K
private def right : Comb := Comb.app (Comb.app .K .Y) .K
private def t : Comb := Comb.app left right

example :
    ∃ c : Completion t,
      (Quotient.mk (s := (inferInstance : Setoid (LSteps t c.w))) (Completion.leftPath c) :
            (⟨t⟩ : MWQuotObj) ⟶ (⟨c.w⟩ : MWQuotObj)) =
        Quotient.mk (s := (inferInstance : Setoid (LSteps t c.w))) (Completion.rightPath c) := by
  -- Two concrete one-step reductions from `t`, one in each subtree.
  have hLeft : Comb.Step t (Comb.app .S right) := by
    exact Comb.Step.app_left (Comb.Step.K_rule (x := .S) (y := .K))
  have hRight : Comb.Step t (Comb.app left .Y) := by
    exact Comb.Step.app_right (Comb.Step.K_rule (x := .Y) (y := .K))
  -- Convert to labeled edges, then build a completion cell.
  rcases PathTruncation.nonempty_lstep_of_step (t := t) (u := Comb.app .S right) hLeft with ⟨l⟩
  rcases PathTruncation.nonempty_lstep_of_step (t := t) (u := Comb.app left .Y) hRight with ⟨r⟩
  rcases Completion.nonempty_of_fork l r with ⟨c⟩
  refine ⟨c, ?_⟩
  simpa using CompletionHomotopy.quot_eq_of_completion c

end LoF
end Tests
end HeytingLean
