import HeytingLean.Numbers.Surreal.Birthday.FullChain

namespace HeytingLean.Embeddings

open HeytingLean.Numbers.Surreal.Birthday
open HeytingLean.Numbers.SurrealCore in
open HeytingLean.Numbers.Surreal.Birthday in

/-- A metric for the surreal lens on the finite pre-game carrier: a Nat-valued function with
    zero-at-null, sign invariance, subadditivity, and strict decrease on options. -/
structure SurrealLensMetric where
  measure : BirthdayForm → Nat
  zero_at_null : measure HeytingLean.Numbers.SurrealCore.nullCut = 0
  sign_invariant : ∀ x : BirthdayForm,
    measure (HeytingLean.Numbers.SurrealCore.neg x) = measure x
  subadditive : ∀ x y : BirthdayForm,
    measure (HeytingLean.Numbers.SurrealCore.add x y) ≤ measure x + measure y
  option_strict_decrease_L : ∀ (x g : BirthdayForm), g ∈ x.L → measure g < measure x
  option_strict_decrease_R : ∀ (x g : BirthdayForm), g ∈ x.R → measure g < measure x

namespace SurrealLensMetric

open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.Birthday

/-- The birthday metric for the surreal lens: normalizedBirthday satisfies all lens metric axioms. -/
noncomputable def birthday : SurrealLensMetric where
  measure := normalizedBirthday
  zero_at_null := normalizedBirthday_nullCut
  sign_invariant := normalizedBirthday_neg
  subadditive := by
    intro x y
    have h := birthdayAdd_birth_le x y
    show normalizedBirthday (HeytingLean.Numbers.SurrealCore.add x y) ≤
      normalizedBirthday x + normalizedBirthday y
    change (normalize (HeytingLean.Numbers.SurrealCore.add x y)).birth ≤
      normalizedBirthday x + normalizedBirthday y
    simpa [birthdayAdd] using h
  option_strict_decrease_L := by
    intro x g hg; exact normalizedBirthday_left_lt hg
  option_strict_decrease_R := by
    intro x g hg; exact normalizedBirthday_right_lt hg

/-- The surreal lens is enriched with the birthday metric. -/
theorem exists_birthday_metric :
    ∃ m : SurrealLensMetric, m.measure = normalizedBirthday :=
  ⟨birthday, rfl⟩

end SurrealLensMetric
end HeytingLean.Embeddings
