import Mathlib.Tactic.Basic

namespace HeytingLean.Tests.ProofState

theorem sourceFixture_id : ∀ P : Prop, P → P := by
  intro P
  intro hP
  exact hP

theorem sourceFixture_and_left : ∀ P Q : Prop, P ∧ Q → P := by
  intro P Q hPQ
  exact hPQ.left

theorem sourceFixture_and_right : ∀ P Q : Prop, P ∧ Q → Q := by
  intro P Q hPQ
  exact hPQ.right

theorem sourceFixture_or_inl : ∀ P Q : Prop, P → P ∨ Q := by
  intro P Q hP
  exact Or.inl hP

theorem sourceFixture_imp_trans : ∀ P Q R : Prop, (P → Q) → (Q → R) → P → R := by
  intro P Q R hPQ hQR hP
  exact hQR (hPQ hP)

theorem sourceFixture_and_intro : ∀ P Q : Prop, P → Q → P ∧ Q := by
  intro P Q hP hQ
  exact And.intro hP hQ

theorem sourceFixture_or_inr : ∀ P Q : Prop, Q → P ∨ Q := by
  intro P Q hQ
  exact Or.inr hQ

theorem sourceFixture_false_elim : ∀ P : Prop, False → P := by
  intro P hFalse
  exact False.elim hFalse

theorem sourceFixture_imp_swap : ∀ P Q R : Prop, (P → Q → R) → Q → P → R := by
  intro P Q R hPQR hQ hP
  exact hPQR hP hQ

theorem sourceFixture_or_elim : ∀ P Q R : Prop, (P → R) → (Q → R) → P ∨ Q → R := by
  intro P Q R hPR hQR hPQ
  cases hPQ with
  | inl hP => exact hPR hP
  | inr hQ => exact hQR hQ

end HeytingLean.Tests.ProofState
