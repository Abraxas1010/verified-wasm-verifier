import HeytingLean.Quantum.OML.Examples.PropBoolean

-- Sasaki inequality specialized to Prop: a ∧ (¬ a ∨ (a ∧ b)) → b
example (a b : Prop) : a ∧ (¬ a ∨ (a ∧ b)) → b := by
  intro h; cases h with
  | intro ha h2 =>
    cases h2 with
    | inl hna => exact False.elim (hna ha)
    | inr hab => exact And.right hab
