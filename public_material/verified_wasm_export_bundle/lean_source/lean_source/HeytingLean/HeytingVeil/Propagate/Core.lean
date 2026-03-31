/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Temporal.Core
import HeytingLean.HeytingVeil.Verify.Core

/-!
# HeytingVeil Propagate Core

Minimal invariant-transport layer:
- simulation map between source and target machines,
- pullback of target invariants onto source states,
- transport of inductive certificates along that simulation.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Propagate

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify

universe u v

variable {SrcState : Type u} {TgtState : Type v}

/-- Forward simulation from source machine states into target machine states. -/
structure Simulation (Msrc : Machine SrcState) (Mtgt : Machine TgtState)
    (encode : SrcState → TgtState) : Prop where
  init_preserved : ∀ s : SrcState, Msrc.Init s → Mtgt.Init (encode s)
  step_preserved : ∀ s t : SrcState, Msrc.Step s t → Mtgt.Step (encode s) (encode t)

/-- Pull a target invariant back along an encoding map. -/
def pullbackInv (encode : SrcState → TgtState) (Inv : TgtState → Prop) : SrcState → Prop :=
  fun s => Inv (encode s)

@[simp] theorem pullbackInv_apply (encode : SrcState → TgtState) (Inv : TgtState → Prop)
    (s : SrcState) : pullbackInv encode Inv s ↔ Inv (encode s) := Iff.rfl

/-- Transport an inductive invariant certificate from target machine to source machine. -/
def pullbackInvariantCert {Msrc : Machine SrcState} {Mtgt : Machine TgtState}
    {encode : SrcState → TgtState} {Inv : TgtState → Prop}
    (sim : Simulation Msrc Mtgt encode) (cert : InvariantCert Mtgt Inv) :
    InvariantCert Msrc (pullbackInv encode Inv) where
  init_holds := by
    intro s hs
    exact cert.init_holds (encode s) (sim.init_preserved s hs)
  step_preserves := by
    intro s t hs hstep
    exact cert.step_preserves (encode s) (encode t) hs (sim.step_preserved s t hstep)

end Propagate
end HeytingVeil
end HeytingLean
