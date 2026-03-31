/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Temporal.Core

/-!
# Decidable Model-Checking Surface

Computable finite-state wrapper around `Temporal.Machine`.
-/

namespace HeytingLean
namespace HeytingVeil
namespace ModelCheck

open HeytingLean.HeytingVeil.Temporal

universe u

/-- A finite-state machine with decidable `Init` and `Step`. -/
structure DecidableMachine (State : Type u) [DecidableEq State] where
  machine : Machine State
  states : List State
  decInit : DecidablePred machine.Init
  decStep : ∀ s t : State, Decidable (machine.Step s t)

/-- Decidable invariant candidate. -/
structure DecidableInvCandidate (State : Type u) where
  inv : State → Prop
  decInv : DecidablePred inv

attribute [instance] DecidableMachine.decInit
attribute [instance] DecidableInvCandidate.decInv

/-- Enumerated initial states of a decidable machine. -/
def initStates {State : Type u} [DecidableEq State] (dm : DecidableMachine State) : List State :=
  dm.states.filter (fun s => decide (dm.machine.Init s))

/-- Enumerated successors of `s` using the finite state universe. -/
def successors {State : Type u} [DecidableEq State] (dm : DecidableMachine State) (s : State) : List State :=
  dm.states.filter (fun t => by
    haveI : Decidable (dm.machine.Step s t) := dm.decStep s t
    exact decide (dm.machine.Step s t))

end ModelCheck
end HeytingVeil
end HeytingLean
