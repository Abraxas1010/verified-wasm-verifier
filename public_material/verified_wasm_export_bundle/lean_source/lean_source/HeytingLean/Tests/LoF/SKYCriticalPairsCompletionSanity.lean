import HeytingLean.LoF.Combinators.Category.CompletionFromCriticalPairs

/-!
# Smoke test: extracting completion cells/2-cells from `StepAt` peaks

This file checks that a concrete `Comb.StepAt.Peak` can be turned into a multiway completion cell,
using the `CompletionFromCriticalPairs` bridge.
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
    (∃ c : Completion t, c.joinLeft.length ≤ 2 ∧ c.joinRight.length ≤ 2) ∧
    (∃ c : Completion t, Nonempty (Completion2Cell (Completion.leftPath c) (Completion.rightPath c))) := by
  have hLeft : Comb.Step t (Comb.app .S right) := by
    exact Comb.Step.app_left (Comb.Step.K_rule (x := .S) (y := .K))
  have hRight : Comb.Step t (Comb.app left .Y) := by
    exact Comb.Step.app_right (Comb.Step.K_rule (x := .Y) (y := .K))

  rcases Comb.Step.exists_stepAt (t := t) (u := Comb.app .S right) hLeft with ⟨r₁, p₁, hat₁⟩
  rcases Comb.Step.exists_stepAt (t := t) (u := Comb.app left .Y) hRight with ⟨r₂, p₂, hat₂⟩

  let pk : Comb.StepAt.Peak t :=
    { u := Comb.app .S right
      v := Comb.app left .Y
      r₁ := r₁
      p₁ := p₁
      r₂ := r₂
      p₂ := p₂
      left := hat₁
      right := hat₂ }

  refine ⟨?_, ?_⟩
  · exact StepAtPeak.exists_completion_len_le2 (t := t) pk
  · exact StepAtPeak.exists_completion2Cell (t := t) pk

end LoF
end Tests
end HeytingLean
