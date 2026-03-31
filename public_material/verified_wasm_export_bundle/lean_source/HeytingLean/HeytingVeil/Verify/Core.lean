/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Temporal.Core

/-!
# HeytingVeil Verify Core

A minimal verification-loop interface for Phase-3:
- inductive invariant certificates,
- CTI witnesses (counterexample to induction),
- one-step invariant refinement hook.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Verify

open HeytingLean.HeytingVeil.Temporal

universe u

variable {State : Type u}

/-- Certificate that `Inv` is an inductive invariant for machine `M`. -/
structure InvariantCert (M : Machine State) (Inv : State → Prop) : Prop where
  init_holds : ∀ s : State, M.Init s → Inv s
  step_preserves : ∀ s t : State, Inv s → M.Step s t → Inv t

/-- A CTI witness (counterexample to induction) for candidate `Inv`. -/
structure CTI (M : Machine State) (Inv : State → Prop) where
  pre : State
  next : State
  pre_inv : Inv pre
  step : M.Step pre next
  next_not_inv : ¬ Inv next

/-- Any inductive certificate yields safety on all valid traces. -/
theorem safety_of_certificate {M : Machine State} {Inv : State → Prop}
    (cert : InvariantCert M Inv) {σ : Trace State} (hσ : ValidTrace M σ) : Safety Inv σ := by
  intro n
  induction n with
  | zero =>
      exact cert.init_holds (σ 0) hσ.1
  | succ n ih =>
      exact cert.step_preserves (σ n) (σ (n + 1)) ih (hσ.2 n)

/-- A CTI witness proves the candidate is not inductive. -/
theorem cti_breaks_inductiveness {M : Machine State} {Inv : State → Prop}
    (cti : CTI M Inv) :
    ¬ (∀ s t : State, Inv s → M.Step s t → Inv t) := by
  intro h
  exact cti.next_not_inv (h cti.pre cti.next cti.pre_inv cti.step)

/-- Minimal refinement hook: keep `Inv` and include the CTI target state explicitly. -/
def strengthenWithCTI {M : Machine State} (Inv : State → Prop)
    (cti : CTI M Inv) : State → Prop :=
  fun s => Inv s ∨ s = cti.next

@[simp] theorem strengthenWithCTI_next {M : Machine State} {Inv : State → Prop}
    (cti : CTI M Inv) : strengthenWithCTI Inv cti cti.next := by
  exact Or.inr rfl

/-- The same `(pre,next)` pair cannot immediately reappear as a CTI after strengthening. -/
theorem strengthen_blocks_same_edge {M : Machine State} {Inv : State → Prop}
    (cti : CTI M Inv) :
    ¬ ∃ cti' : CTI M (strengthenWithCTI Inv cti),
      cti'.pre = cti.pre ∧ cti'.next = cti.next := by
  intro h
  rcases h with ⟨cti', hpre, hnext⟩
  have hInvNext : strengthenWithCTI Inv cti cti'.next := by
    rw [hnext]
    exact strengthenWithCTI_next cti
  exact cti'.next_not_inv hInvNext

end Verify
end HeytingVeil
end HeytingLean
