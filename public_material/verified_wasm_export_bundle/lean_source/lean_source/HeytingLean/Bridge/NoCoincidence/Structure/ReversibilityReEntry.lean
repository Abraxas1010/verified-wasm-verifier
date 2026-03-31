import HeytingLean.Bridge.NoCoincidence.Basic.Circuit

namespace HeytingLean.Bridge.NoCoincidence.Structure

open HeytingLean.Bridge.NoCoincidence.Basic

/-- Re-entry witness: reversibility supplies a constructive backward path. -/
def ReEntryWitness (C : RevCircuit n) : Prop :=
  ∀ x, C.evalInv (C.eval x) = x

theorem reversibility_reentry_witness (C : RevCircuit n) :
    ReEntryWitness C := by
  intro x
  exact C.eval_left_inv x

theorem reversibility_gives_backward_solution (C : RevCircuit n) (x : State n) :
    ∃ y, C.eval y = x := by
  refine ⟨C.evalInv x, C.eval_right_inv x⟩

end HeytingLean.Bridge.NoCoincidence.Structure
