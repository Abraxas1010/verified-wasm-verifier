/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Verify.Core

/-!
# CTI Refinement Example

Concrete Gate-3 demonstration:
- candidate invariant fails (CTI exists),
- refine with CTI,
- refined invariant is inductive for this machine.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Verify
namespace Examples

open HeytingLean.HeytingVeil.Temporal

/-- Two-state stabilizing machine over `Nat`: `0 → 1`, `1 → 1`. -/
def stabilizeOneMachine : Machine Nat where
  Init := fun s => s = 0
  Step := fun s t => (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 1)

/-- Initial (too-weak) candidate invariant. -/
def inv0 : Nat → Prop :=
  fun s => s = 0

/-- Explicit CTI for `inv0`: `0 → 1`. -/
def cti0 : CTI stabilizeOneMachine inv0 where
  pre := 0
  next := 1
  pre_inv := by simp [inv0]
  step := by
    left
    simp
  next_not_inv := by
    simp [inv0]

/-- Refined invariant from CTI inclusion hook. -/
def inv1 : Nat → Prop :=
  strengthenWithCTI inv0 cti0

theorem inv1_char (s : Nat) : inv1 s ↔ s = 0 ∨ s = 1 := by
  constructor
  · intro hs
    rcases hs with h0 | h1
    · exact Or.inl h0
    · exact Or.inr h1
  · intro hs
    rcases hs with h0 | h1
    · exact Or.inl h0
    · exact Or.inr h1

/-- `inv1` is inductive for `stabilizeOneMachine`. -/
def inv1_cert : InvariantCert stabilizeOneMachine inv1 where
  init_holds := by
    intro s hs
    left
    exact hs
  step_preserves := by
    intro s t hs hstep
    rcases hstep with h01 | h11
    · right
      exact h01.2
    · right
      exact h11.2

/-- Canonical valid trace: `0,1,1,1,...`. -/
def stabilizeOneTrace : Trace Nat :=
  fun n => if n = 0 then 0 else 1

theorem stabilizeOneTrace_valid : ValidTrace stabilizeOneMachine stabilizeOneTrace := by
  constructor
  · simp [stabilizeOneMachine, stabilizeOneTrace]
  · intro n
    by_cases h0 : n = 0
    · subst h0
      simp [stabilizeOneMachine, stabilizeOneTrace]
    · have hsucc : n + 1 ≠ 0 := Nat.succ_ne_zero n
      simp [stabilizeOneMachine, stabilizeOneTrace, h0]

/-- End-to-end slice: CTI exists for `inv0`; certificate exists for refined `inv1`. -/
theorem verify_cti_refine_verify_demo :
    (∃ _ : CTI stabilizeOneMachine inv0, True) ∧
    (∃ _ : InvariantCert stabilizeOneMachine inv1, True) := by
  constructor
  · exact ⟨cti0, trivial⟩
  · exact ⟨inv1_cert, trivial⟩

end Examples
end Verify
end HeytingVeil
end HeytingLean
