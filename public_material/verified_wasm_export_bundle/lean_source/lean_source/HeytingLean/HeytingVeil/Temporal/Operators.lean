import HeytingLean.HeytingVeil.Temporal.Trace

namespace HeytingLean.HeytingVeil.Temporal

variable {α : Type u}

def Always (P : StatePred α) (tr : Trace α) : Prop :=
  ∀ n, P (tr n)

def EventuallyState (P : StatePred α) (tr : Trace α) : Prop :=
  ∃ n, P (tr n)

def LeadsTo (P Q : StatePred α) (tr : Trace α) : Prop :=
  ∀ n, P (tr n) → ∃ m, n ≤ m ∧ Q (tr m)

end HeytingLean.HeytingVeil.Temporal
