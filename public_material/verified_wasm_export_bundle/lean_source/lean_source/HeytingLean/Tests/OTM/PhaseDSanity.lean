import HeytingLean.OTM.NoneistSemantics

namespace HeytingLean.Tests.OTM

open HeytingLean.OTM

universe u v

variable {ι : Type u} {α : Type v}
variable [DecidableEq ι] [LoF.PrimaryAlgebra α]

example (M : Machine ι α) :
    otm_state_welltyped (initialNoneistState M) :=
  initialNoneistState_welltyped M

example (S : NoneistState ι α) (hS : otm_state_welltyped S) :
    otm_state_welltyped (noneistStep S) :=
  otm_transition_preserves_noneist_wellformedness S hS

example (M : Machine ι α) (fuel : Nat) :
    otm_state_welltyped (noneistRun fuel (initialNoneistState M)) :=
  (otm_noneist_states_witness (M := M) (mode := .manifest) fuel).1

example (M : Machine ι α) (fuel : Nat) :
    (noneistRun fuel (initialNoneistState M)).machine = Machine.run fuel M :=
  (otm_noneist_states_witness (M := M) (mode := .manifest) fuel).2

end HeytingLean.Tests.OTM
