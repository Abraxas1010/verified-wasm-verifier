import HeytingLean.PerspectivalPlenum.ReReentryTower
import Mathlib.Order.Nucleus

/-!
# RatchetStep ↔ Nucleus structural parallel

A `RatchetStep α` on a frame `α` is a function `Nucleus α → Nucleus α` that is:
- **Extensive**: `∀ J, J ≤ S J`
- **Monotone**: `Monotone S`
- **Idempotent**: `∀ J, S (S J) = S J`

These are exactly the axioms of a nucleus (closure operator) on the poset
of nuclei. This module makes the parallel explicit.

## Key insight

The ratchet is a "second-order nucleus": it operates on the space of nuclei
the same way a nucleus operates on a frame. This means ratchet iteration
(`RatchetTower`) is an instance of nucleus-style fixed-point theory lifted
one categorical level.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet

universe u

variable {α : Type u} [Order.Frame α]

open HeytingLean.PerspectivalPlenum

/-! ## Nucleus axiom witnesses for RatchetStep -/

/-- A RatchetStep is extensive on nuclei. -/
theorem ratchetStep_extensive (S : RatchetStep α) :
    ∀ J : Nucleus α, J ≤ S.step J :=
  S.extensive

/-- A RatchetStep is monotone on nuclei. -/
theorem ratchetStep_monotone (S : RatchetStep α) :
    Monotone S.step :=
  S.monotone

/-- A RatchetStep is idempotent on nuclei. -/
theorem ratchetStep_idempotent (S : RatchetStep α) :
    ∀ J : Nucleus α, S.step (S.step J) = S.step J :=
  S.idempotent

/-- A RatchetStep satisfies all three nucleus axioms on the poset of nuclei.
    This is the structural parallel: `RatchetStep α ≅ "Nucleus on Nucleus α"`. -/
theorem ratchetStep_is_nucleus_on_nuclei (S : RatchetStep α) :
    (∀ J : Nucleus α, J ≤ S.step J) ∧
    (Monotone S.step) ∧
    (∀ J : Nucleus α, S.step (S.step J) = S.step J) :=
  ⟨S.extensive, S.monotone, S.idempotent⟩

/-! ## Fixed-point characterization -/

/-- The fixed points of a RatchetStep are the nuclei that are "fully ratcheted". -/
def isRatchetFixed (S : RatchetStep α) (J : Nucleus α) : Prop :=
  S.step J = J

/-- The base nucleus of a RatchetTower is a fixed point iff the step is trivial on it. -/
theorem ratchetTower_layer_fixed (T : RatchetTower α) (n : Nat) :
    T.step.step (RatchetStep.iterate T.step n T.base) =
    RatchetStep.iterate T.step n T.base →
    isRatchetFixed T.step (RatchetStep.iterate T.step n T.base) :=
  id

/-- After one application, the result is always a fixed point (by idempotence). -/
theorem ratchetStep_apply_is_fixed (S : RatchetStep α) (J : Nucleus α) :
    isRatchetFixed S (S.step J) := by
  exact S.idempotent J

/-! ## RatchetTower convergence -/

/-- A RatchetTower converges after one step: `layer 1 = layer n` for all `n ≥ 1`. -/
theorem ratchetTower_converges_at_one (T : RatchetTower α) (n : Nat) :
    T.layer (n + 1) = T.layer 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      -- layer (n+2) = S (iterate S (n+1) base) = S (layer (n+1)) = S (layer 1) = S (S base)
      -- By IH, layer (n+1) = layer 1 = S base.
      -- So layer (n+2) = S (S base) = S base = layer 1 (by idempotence).
      show T.layer (n + 1 + 1) = T.layer 1
      have h1 : T.layer (n + 1 + 1) = T.step.step (T.layer (n + 1)) := rfl
      rw [h1, ih]
      -- Goal: T.step.step (T.layer 1) = T.layer 1
      -- T.layer 1 = T.step.step T.base, so this is idempotence.
      exact T.step.idempotent T.base

/-! ## Composition preserves the nucleus-on-nuclei structure -/

/-- Composing compatible RatchetSteps preserves extensiveness. -/
theorem compose_extensive (S T : RatchetStep α) (h : RatchetCompatibility S T) :
    ∀ J : Nucleus α, J ≤ (RatchetStep.compose S T h).step J := by
  intro J
  exact (RatchetStep.compose S T h).extensive J

/-- Composing compatible RatchetSteps preserves idempotence. -/
theorem compose_idempotent (S T : RatchetStep α) (h : RatchetCompatibility S T) :
    ∀ J : Nucleus α, (RatchetStep.compose S T h).step ((RatchetStep.compose S T h).step J) =
      (RatchetStep.compose S T h).step J := by
  intro J
  exact (RatchetStep.compose S T h).idempotent J

end JRatchet
end Bridges
end HeytingLean
