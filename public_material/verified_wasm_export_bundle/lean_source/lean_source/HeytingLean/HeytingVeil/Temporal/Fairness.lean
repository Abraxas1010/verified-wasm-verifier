import HeytingLean.HeytingVeil.Temporal.Stuttering

namespace HeytingLean.HeytingVeil.Temporal

variable {α : Type u}

def OccursInfinitelyOften (P : Nat → Prop) : Prop :=
  ∀ n, ∃ m, n ≤ m ∧ P m

/-- Sprint obligation `HV.Temporal.EnabledDefStable`. -/
theorem enabledDefStable (R : StepRel α) (s : α) :
    Enabled R s = (∃ s', R s s') := rfl

end HeytingLean.HeytingVeil.Temporal
