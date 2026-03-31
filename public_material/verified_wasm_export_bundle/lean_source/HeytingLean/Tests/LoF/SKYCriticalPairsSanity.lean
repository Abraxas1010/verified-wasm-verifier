import HeytingLean.LoF.Combinators.Rewriting.CriticalPairs

/-!
# Smoke test: critical-peak wrapper for `StepAt` local confluence

This file checks that the `CriticalPairs` wrapper is usable on a concrete example:

- build a `StepAt.Peak t` from two concrete `Step` reductions out of `t`, and
- extract joinability (including the bounded `≤ 2` join witness).
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb

private def left : Comb := Comb.app (Comb.app .K .S) .K
private def right : Comb := Comb.app (Comb.app .K .Y) .K
private def t : Comb := Comb.app left right

example :
    ∃ pk : Comb.StepAt.Peak t,
      (∃ w : Comb, Comb.Steps pk.u w ∧ Comb.Steps pk.v w) ∧
      (∃ w : Comb, Comb.StepsUpTo2 pk.u w ∧ Comb.StepsUpTo2 pk.v w) := by
  -- Two concrete one-step reductions from `t`, one in each subtree.
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

  refine ⟨pk, ?_, ?_⟩
  · exact Comb.StepAt.Peak.joinable pk
  · exact Comb.StepAt.Peak.joinable_upTo2 pk

end LoF
end Tests
end HeytingLean

