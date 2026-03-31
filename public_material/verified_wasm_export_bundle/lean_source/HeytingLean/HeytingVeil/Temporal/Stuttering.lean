import HeytingLean.HeytingVeil.Temporal.Operators

namespace HeytingLean.HeytingVeil.Temporal

variable {α : Type u}

def StutterStep (R : StepRel α) (s s' : α) : Prop :=
  s' = s ∨ R s s'

/-- Sprint obligation `HV.Temporal.StutterClosedInvariant`. -/
theorem stutterClosedInvariant
    {R : StepRel α} {I : StatePred α}
    (hStep : ∀ s s', R s s' → I s → I s') :
    ∀ s s', StutterStep R s s' → I s → I s' := by
  intro s s' h hs
  rcases h with rfl | hR
  · exact hs
  · exact hStep s s' hR hs

end HeytingLean.HeytingVeil.Temporal
