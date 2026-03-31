import Mathlib.Tactic
import HeytingLean.LoF.Combinators.Category.CompletionCells

/-!
Compile + eval sanity checks for `CompletionCells` (local diamonds).

We exhibit a small term with two disjoint `K`-redexes (left vs right subtree) so that reducing either
first yields a joinable “diamond”.
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

-- Show a concrete diamond summary (exact witness chosen depends on enumeration order).
#eval (findDiamond1? t).map (fun d => d.summary)

-- Hard assertion: at least one 1-step diamond exists for this `t`.
example : (findDiamond1? t).isSome = true := by
  native_decide

-- Bounded join search / completion cell (fork + multi-step join).
#eval (findCompletion? t 2).map (fun c => c.summary)

example : (findCompletion? t 2).isSome = true := by
  native_decide

/-! ## Proof-based completion (non-search) -/

-- Even without any bounded search, any two 1-step edges out of `t` have a completion cell.
example : Nonempty (Completion t) := by
  -- Two concrete one-step reductions from `t`, one in each subtree.
  have hLeft : Comb.Step t (Comb.app .S right) := by
    -- Reduce the left `K`-redex, then lift through the outer application.
    exact Comb.Step.app_left (Comb.Step.K_rule (x := .S) (y := .K))
  have hRight : Comb.Step t (Comb.app left .Y) := by
    -- Reduce the right `K`-redex, then lift through the outer application.
    exact Comb.Step.app_right (Comb.Step.K_rule (x := .Y) (y := .K))
  -- Convert `Step` to labeled `LStep` (existentially), then apply the proof-based completion lemma.
  rcases PathTruncation.nonempty_lstep_of_step (t := t) (u := Comb.app .S right) hLeft with ⟨l⟩
  rcases PathTruncation.nonempty_lstep_of_step (t := t) (u := Comb.app left .Y) hRight with ⟨r⟩
  exact Completion.nonempty_of_fork l r

-- Stronger: the join legs can always be chosen with length ≤ 2.
example : ∃ c : Completion t, c.joinLeft.length ≤ 2 ∧ c.joinRight.length ≤ 2 := by
  have hLeft : Comb.Step t (Comb.app .S right) := by
    exact Comb.Step.app_left (Comb.Step.K_rule (x := .S) (y := .K))
  have hRight : Comb.Step t (Comb.app left .Y) := by
    exact Comb.Step.app_right (Comb.Step.K_rule (x := .Y) (y := .K))
  rcases PathTruncation.nonempty_lstep_of_step (t := t) (u := Comb.app .S right) hLeft with ⟨l⟩
  rcases PathTruncation.nonempty_lstep_of_step (t := t) (u := Comb.app left .Y) hRight with ⟨r⟩
  exact Completion.exists_of_fork_len_le2 l r

end LoF
end Tests
end HeytingLean
