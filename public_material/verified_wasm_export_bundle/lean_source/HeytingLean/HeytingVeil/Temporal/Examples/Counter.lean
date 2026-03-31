/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Temporal.Core

/-!
# HeytingVeil Temporal Counter Example

A concrete machine instance for Gate-0 execution:
- one valid trace,
- one safety theorem,
- one liveness theorem,
- one fairness theorem.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Temporal
namespace Examples

/-- Counter starts at `0` and increments by `1` each step. -/
def counterMachine : Machine Nat where
  Init := fun s => s = 0
  Step := fun s t => t = s + 1

/-- Canonical counter trace. -/
def counterTrace : Trace Nat :=
  fun n => n

theorem counterTrace_valid : ValidTrace counterMachine counterTrace := by
  constructor
  · rfl
  · intro n
    simp [counterMachine, counterTrace]

theorem counterTrace_safety_nonneg : Safety (fun s : Nat => 0 ≤ s) counterTrace := by
  intro n
  exact Nat.zero_le n

theorem counterTrace_liveness_eventually_ge (k : Nat) :
    Eventually (fun n => k ≤ counterTrace n) := by
  refine ⟨k, ?_⟩
  simp [counterTrace]

theorem counterTrace_weakFair : WeakFair counterMachine.Step counterTrace := by
  intro _
  intro n
  refine ⟨n, Nat.le_refl _, ?_⟩
  simp [counterMachine, counterTrace]

end Examples
end Temporal
end HeytingVeil
end HeytingLean
