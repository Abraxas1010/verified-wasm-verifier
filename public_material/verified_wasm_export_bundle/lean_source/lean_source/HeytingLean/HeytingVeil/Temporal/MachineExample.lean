import HeytingLean.HeytingVeil.Temporal.Fairness

namespace HeytingLean.HeytingVeil.Temporal

abbrev CounterState := Nat

def counterTrace : Trace CounterState := fun n => n

def nextCounter : StepRel CounterState := fun s s' => s' = s + 1

def safeCounter : StatePred CounterState := fun s => 0 ≤ s

def goalAt (k : Nat) : StatePred CounterState := fun s => s = k

theorem counterNextStep (n : Nat) :
    nextCounter (counterTrace n) (counterTrace (n + 1)) := by
  simp [nextCounter, counterTrace]

end HeytingLean.HeytingVeil.Temporal
