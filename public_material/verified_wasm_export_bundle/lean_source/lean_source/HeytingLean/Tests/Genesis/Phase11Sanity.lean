import HeytingLean.Genesis

/-!
# Genesis Phase 11 Sanity

Observer-v2 constrained update checks.
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis

#check ConstraintState
#check ConstraintState.assign
#check constraintsOfObserver
#check ObserverV2.fromObserver
#check reinforceChoice
#check reinforceChoice_preserves_defaultCompletion

def obs1 : Observer where
  depth := 1
  choices := fun _ => true
  phase := phaseJ

def obs1v2 : ObserverV2 := ObserverV2.fromObserver obs1

example : obs1v2.toObserver = obs1 := by
  rfl

example :
    ConstraintState.agrees obs1v2.constraints (defaultCompletion obs1v2.base) := by
  simpa [obs1v2] using constraintsOfObserver_agrees_defaultCompletion obs1

example :
    ConstraintState.agrees
      (reinforceChoice obs1v2 ⟨0, by decide⟩).constraints
      (defaultCompletion obs1v2.base) := by
  apply reinforceChoice_preserves_defaultCompletion
  simpa [obs1v2] using constraintsOfObserver_agrees_defaultCompletion obs1

end HeytingLean.Tests.Genesis

