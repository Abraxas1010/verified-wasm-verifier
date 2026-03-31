import HeytingLean.LoF.Combinators.Category.Completion2Cell

/-!
# Smoke test: completion 2-cells as explicit data

This file checks that:

- a concrete 1-step fork produces a completion square, and
- that square yields a `Completion2Cell` witness whose forgetting lands in `CompletionHomotopy`.
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
    ∃ c : Completion t, Completion2Cell (Completion.leftPath c) (Completion.rightPath c) := by
  have hLeft : Comb.Step t (Comb.app .S right) := by
    exact Comb.Step.app_left (Comb.Step.K_rule (x := .S) (y := .K))
  have hRight : Comb.Step t (Comb.app left .Y) := by
    exact Comb.Step.app_right (Comb.Step.K_rule (x := .Y) (y := .K))
  rcases PathTruncation.nonempty_lstep_of_step (t := t) (u := Comb.app .S right) hLeft with ⟨l⟩
  rcases PathTruncation.nonempty_lstep_of_step (t := t) (u := Comb.app left .Y) hRight with ⟨r⟩
  rcases Completion.nonempty_of_fork l r with ⟨c⟩
  exact ⟨c, Completion2Cell.of_completion c⟩

example (c : Completion t) :
    CompletionHomotopy (Completion.leftPath c) (Completion.rightPath c) := by
  -- Forgetting any `Completion2Cell` witness yields a `CompletionHomotopy`.
  exact (Completion2Cell.toHomotopy (Completion2Cell.of_completion c))

end LoF
end Tests
end HeytingLean

