/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Temporal.Core
import HeytingLean.HeytingVeil.Verify.Core

/-!
# HeytingVeil ModelCheck Core

Bounded checker interface for Phase-3:
- scans a finite prefix for an induction counterexample edge,
- emits a witness in `Verify.CTI` shape.
-/

namespace HeytingLean
namespace HeytingVeil
namespace ModelCheck

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify

universe u

variable {State : Type u}

/-- Scan a finite path and return the first CTI edge, if any. -/
noncomputable def findCTIOnPath (M : Machine State) (Inv : State → Prop) :
    List State → Option (CTI M Inv)
  | [] => none
  | [_] => none
  | s :: t :: rest =>
      by
        classical
        by_cases h : Inv s ∧ M.Step s t ∧ ¬ Inv t
        · exact some {
            pre := s
            next := t
            pre_inv := h.1
            step := h.2.1
            next_not_inv := h.2.2
          }
        · exact findCTIOnPath M Inv (t :: rest)

/-- Result bundle for bounded CTI search. -/
structure BoundedCheckResult (M : Machine State) (Inv : State → Prop) where
  bound : Nat
  exploredPath : List State
  cti? : Option (CTI M Inv)

/-- Bounded CTI check over the prefix of length `bound + 1` of a candidate path. -/
noncomputable def checkPathWithin (M : Machine State) (Inv : State → Prop)
    (bound : Nat) (path : List State) : BoundedCheckResult M Inv :=
  {
    bound := bound
    exploredPath := path.take (bound + 1)
    cti? := findCTIOnPath M Inv (path.take (bound + 1))
  }

/-- Soundness: any produced CTI witness refutes one-step inductiveness. -/
theorem checkPathWithin_sound {M : Machine State} {Inv : State → Prop}
    {bound : Nat} {path : List State} {cti : CTI M Inv}
    (_h : (checkPathWithin M Inv bound path).cti? = some cti) :
    ¬ (∀ s t : State, Inv s → M.Step s t → Inv t) := by
  exact cti_breaks_inductiveness cti

end ModelCheck
end HeytingVeil
end HeytingLean
