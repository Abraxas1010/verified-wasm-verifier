/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.ModelCheck.Core
import HeytingLean.HeytingVeil.Verify.Examples.CounterexampleRefinement

/-!
# Bounded CTI Example

Concrete bounded-check run that produces a CTI witness compatible with
`HeytingVeil.Verify.CTI`.
-/

namespace HeytingLean
namespace HeytingVeil
namespace ModelCheck
namespace Examples

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify
open HeytingLean.HeytingVeil.Verify.Examples

/-- Bounded run finds a CTI for the weak candidate `inv0`. -/
theorem bounded_finds_cti :
    ∃ cti : CTI stabilizeOneMachine inv0,
      (checkPathWithin stabilizeOneMachine inv0 2 [0, 1, 1]).cti? = some cti := by
  unfold checkPathWithin
  simp [findCTIOnPath, stabilizeOneMachine, inv0]

/-- Any CTI returned by bounded checking breaks inductiveness of `inv0`. -/
theorem bounded_cti_breaks_inv0 :
    ∀ {cti : CTI stabilizeOneMachine inv0},
      (checkPathWithin stabilizeOneMachine inv0 2 [0, 1, 1]).cti? = some cti →
        ¬ (∀ s t : Nat, inv0 s → stabilizeOneMachine.Step s t → inv0 t) := by
  intro cti h
  exact checkPathWithin_sound (M := stabilizeOneMachine) (Inv := inv0) (bound := 2)
    (path := [0, 1, 1]) h

end Examples
end ModelCheck
end HeytingVeil
end HeytingLean
