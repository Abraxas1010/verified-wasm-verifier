import HeytingLean.HeytingVeil.Temporal.MachineExample

namespace HeytingLean.HeytingVeil.Temporal

/-- Sprint obligation `HV.Temporal.SafetyExample`. -/
theorem safetyExample : Always safeCounter counterTrace := by
  intro n
  exact Nat.zero_le n

/-- Sprint obligation `HV.Temporal.ProgressExample`. -/
theorem progressExample (k : Nat) : EventuallyState (goalAt k) counterTrace := by
  refine ⟨k, ?_⟩
  simp [goalAt, counterTrace]

/-- Sprint obligation `HV.Temporal.WFImpliesProgressExample`. -/
theorem wfImpliesProgressExample (k : Nat)
    (_hWF : WeakFair nextCounter counterTrace) : EventuallyState (goalAt k) counterTrace := by
  exact progressExample k

end HeytingLean.HeytingVeil.Temporal
