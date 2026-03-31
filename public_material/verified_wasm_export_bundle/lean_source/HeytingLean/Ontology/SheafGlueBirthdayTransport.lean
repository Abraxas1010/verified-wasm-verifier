import HeytingLean.Numbers.Surreal.Birthday.FullChain

namespace HeytingLean.Ontology

open HeytingLean.Numbers.Surreal.Birthday
open HeytingLean.Numbers.SurrealCore

/-- Birthday cost of a unary transport operation: output birthday ≤ bound(input birthday). -/
structure BirthdayBoundedOp where
  op : BirthdayForm → BirthdayForm
  bound : Nat → Nat
  bound_holds : ∀ g : BirthdayForm, normalizedBirthday (op g) ≤ bound (normalizedBirthday g)

/-- Birthday cost of a binary transport operation: output birthday ≤ bound(input birthdays). -/
structure BirthdayBoundedBinOp where
  op : BirthdayForm → BirthdayForm → BirthdayForm
  bound : Nat → Nat → Nat
  bound_holds : ∀ x y : BirthdayForm,
    normalizedBirthday (op x y) ≤ bound (normalizedBirthday x) (normalizedBirthday y)

/-- Negation transport has zero cost (birthday-preserving). -/
noncomputable def negTransport : BirthdayBoundedOp where
  op := HeytingLean.Numbers.SurrealCore.neg
  bound := id
  bound_holds := by
    intro g
    have h := normalizedBirthday_neg g
    simp only [normalizedBirthday_eq] at h
    exact le_of_eq h

/-- Addition transport is subadditive (birthday ≤ sum of inputs). -/
noncomputable def addTransport : BirthdayBoundedBinOp where
  op := HeytingLean.Numbers.SurrealCore.add
  bound := fun a b => a + b
  bound_holds := by
    intro x y
    have h := birthdayAdd_birth_le x y
    change (normalize (HeytingLean.Numbers.SurrealCore.add x y)).birth ≤
      normalizedBirthday x + normalizedBirthday y
    simpa [birthdayAdd] using h

/-- Subtraction transport: birthday ≤ sum of inputs (from neg invariance + add subadditivity). -/
noncomputable def subTransport : BirthdayBoundedBinOp where
  op := fun x y => HeytingLean.Numbers.SurrealCore.add x (HeytingLean.Numbers.SurrealCore.neg y)
  bound := fun a b => a + b
  bound_holds := by
    intro x y
    exact normalizedBirthday_sub_raw_le x y

/-- Negation is an exact isometry (birthday is preserved, not just bounded). -/
theorem negTransport_exact (g : BirthdayForm) :
    normalizedBirthday (HeytingLean.Numbers.SurrealCore.neg g) = normalizedBirthday g :=
  normalizedBirthday_neg g

end HeytingLean.Ontology
