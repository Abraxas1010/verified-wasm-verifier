/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.ModelCheck.VerifyLoop

/-!
# Executable Counter / Stabilize-One Checks

`#eval` surfaces proving the bounded checker is executable (not classical-only).
-/

namespace HeytingLean
namespace HeytingVeil
namespace ModelCheck
namespace Examples

open HeytingLean.HeytingVeil.Temporal

/-- Counter machine over bounded naturals. -/
def counterMachine : Machine Nat where
  Init := fun s => s = 0
  Step := fun s t => t = s + 1

/-- Two-state stabilize machine: 0→1, 1→1. -/
def stabilizeOneMachine : Machine Nat where
  Init := fun s => s = 0
  Step := fun s t => (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 1)

/-- Decidable wrapper for bounded counter states 0..6. -/
def counterDecidable : DecidableMachine Nat :=
  {
    machine := counterMachine
    states := [0, 1, 2, 3, 4, 5, 6]
    decInit := by
      intro s
      simpa [counterMachine] using (inferInstance : Decidable (s = 0))
    decStep := by
      intro s t
      simpa [counterMachine] using (inferInstance : Decidable (t = s + 1))
  }

/-- Decidable wrapper for stabilize-one finite region. -/
def stabilizeOneDecidable : DecidableMachine Nat :=
  {
    machine := stabilizeOneMachine
    states := [0, 1]
    decInit := by
      intro s
      simpa [stabilizeOneMachine] using (inferInstance : Decidable (s = 0))
    decStep := by
      intro s t
      simpa [stabilizeOneMachine] using
        (inferInstance : Decidable ((s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 1)))
  }

/-- Candidate invariant for counter: nonnegative. -/
def invCounter : DecidableInvCandidate Nat :=
  {
    inv := fun s => s ≥ 0
    decInv := by
      intro s
      infer_instance
  }

/-- Too-weak stabilize invariant: only state 0. -/
def inv0 : DecidableInvCandidate Nat :=
  {
    inv := fun s => s = 0
    decInv := by
      intro s
      infer_instance
  }

/-- Expect `true`: bounded counter has no CTI for `s ≥ 0`. -/
def counterNoCTIWithin6 : Bool :=
  match findCTIReachable counterDecidable invCounter 6 with
  | some _ => false
  | none => true

/-- Expect `true`: stabilizeOne has CTI for `s = 0`. -/
def stabilizeHasCTI : Bool :=
  match findCTIReachable stabilizeOneDecidable inv0 2 with
  | some _ => true
  | none => false

/-- Executable refinement summary: should block `1` and terminate without unresolved CTI. -/
def stabilizeRefineSummary : VerifyRefineSummary Nat :=
  verifyRefineLoop stabilizeOneDecidable inv0 2 2

#eval counterNoCTIWithin6
#eval stabilizeHasCTI
#eval stabilizeRefineSummary

end Examples
end ModelCheck
end HeytingVeil
end HeytingLean
