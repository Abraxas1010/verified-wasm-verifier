import HeytingLean.Logic.Plausibility

/-
Bayes = residual on Boolean fragments.
This file stays lightweight and does not alter the core re-entry definitions.
-/

namespace HeytingLean
namespace Logic

open HeytingLean.LoF

/-! ### Numeric Bayes = residual on Boolean fragments -/

section BooleanMeasure

variable {α : Type u} [PrimaryAlgebra α]
variable (R : HeytingLean.LoF.Reentry α)
variable (μ : StrictPlausibilityMeasure (R := R) (S := ennrealScale))
variable [BooleanAlgebra R.Omega]

/-- On a Boolean fragment, strict ENNReal measures send implication to division. -/
lemma StrictPlausibilityMeasure.himp_div_boolean {a b : R.Omega}
    (ha : μ.toPlausibilityMeasure.μ a ≠ 0) :
    μ.toPlausibilityMeasure.μ (a ⇨ b) =
      μ.toPlausibilityMeasure.μ b / μ.toPlausibilityMeasure.μ a :=
  μ.himp_div ha

end BooleanMeasure

/-- A lightweight “classical window” inside a Heyting algebra:
closed under the Heyting connectives, with double negation collapsing. This is
an opt-in helper for Boolean fragments of a larger Heyting world. -/
structure ClassicalWindow (α : Type u) [HeytingAlgebra α] where
  carrier : Set α
  nonempty : carrier.Nonempty
  closed_top : ⊤ ∈ carrier
  closed_bot : ⊥ ∈ carrier
  closed_inf : ∀ {a b}, a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier
  closed_sup : ∀ {a b}, a ∈ carrier → b ∈ carrier → a ⊔ b ∈ carrier
  closed_himp : ∀ {a b}, a ∈ carrier → b ∈ carrier → (a ⇨ b) ∈ carrier
  double_neg_eq : ∀ {a}, a ∈ carrier → ((a ⇨ ⊥) ⇨ ⊥) = a

end Logic
end HeytingLean
