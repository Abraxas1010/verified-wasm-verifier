import Mathlib.Tactic.Basic

namespace HeytingLean.Tests.ProofState

theorem sourceFixtureFamily2_iff_mp : ∀ P Q : Prop, (P ↔ Q) → P → Q := by
  intro P Q hPQ hP
  exact hPQ.mp hP

theorem sourceFixtureFamily2_iff_mpr : ∀ P Q : Prop, (P ↔ Q) → Q → P := by
  intro P Q hPQ hQ
  exact hPQ.mpr hQ

theorem sourceFixtureFamily2_not_not_intro : ∀ P : Prop, P → ¬¬P := by
  intro P hP hNotP
  exact hNotP hP

theorem sourceFixtureFamily2_and_comm : ∀ P Q : Prop, P ∧ Q → Q ∧ P := by
  intro P Q hPQ
  exact And.intro hPQ.right hPQ.left

theorem sourceFixtureFamily2_or_comm : ∀ P Q : Prop, P ∨ Q → Q ∨ P := by
  intro P Q hPQ
  cases hPQ with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ

end HeytingLean.Tests.ProofState
