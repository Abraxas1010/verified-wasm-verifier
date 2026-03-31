import Mathlib.Order.Heyting.Basic
import HeytingLean.Core.Nucleus
import HeytingLean.IteratedVirtual.SpiralEnergy

/-!
# IteratedVirtual.Bridge.NucleusEnergy

Strict-only, minimal bridge from the helix “tension energy” story to the `HeytingLean.Core.Nucleus`
interface.

We do **not** claim a deep semantic identification of “energy minimization” with nucleus fixed
points. Instead we provide a small verified “piece”:

- a canonical nucleus `nonnegNucleus` on `WithBot ℝ` given by `x ↦ x ⊔ 0`;
- the spiral tension energy, embedded as `some (tensionEnergyAt ...)`, is a fixed point of this
  nucleus because it is nonnegative.

This is a reusable lemma pattern elsewhere in HeytingLean: when you have a provably-nonnegative
quantity `e`, it is stable under the “clamp-to-nonnegative” closure operator.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Bridge

open scoped Classical

open HeytingLean.Core

namespace NonnegNucleus

/-- The “nonnegativity closure” nucleus on `WithBot ℝ`: close by joining with `0`. -/
def nonnegNucleus : Nucleus (WithBot ℝ) where
  R := fun x => x ⊔ (0 : WithBot ℝ)
  extensive := by
    intro x
    exact le_sup_left
  idempotent := by
    intro x
    -- `(x ⊔ 0) ⊔ 0 = x ⊔ 0`
    simp
  meet_preserving := by
    intro x y
    -- `R (x ⊓ y) = (x ⊓ y) ⊔ 0 = (x ⊔ 0) ⊓ (y ⊔ 0) = R x ⊓ R y`
    simpa [sup_comm, sup_left_comm, sup_assoc] using (sup_inf_left (0 : WithBot ℝ) x y)

@[simp] lemma nonnegNucleus_R (x : WithBot ℝ) :
    nonnegNucleus.R x = x ⊔ (0 : WithBot ℝ) :=
  rfl

end NonnegNucleus

namespace SpiralEnergy

open Point3R

/-- Embed a real-valued energy into the nucleus lattice `WithBot ℝ`. -/
def energyWB (t pitch : ℝ) (p : Point3R) : WithBot ℝ :=
  some (tensionEnergyAt t pitch p)

theorem energyWB_fixed (t pitch : ℝ) (p : Point3R) :
    NonnegNucleus.nonnegNucleus.R (energyWB t pitch p) = energyWB t pitch p := by
  -- `tensionEnergyAt` is nonnegative, so `max e 0 = e`.
  have hn : 0 ≤ tensionEnergyAt t pitch p := tensionEnergyAt_nonneg t pitch p
  have h0le : (0 : WithBot ℝ) ≤ energyWB t pitch p := by
    dsimp [energyWB]
    -- Rewrite both sides as coercions from `ℝ`, then lift via `WithBot.coe_le_coe`.
    change ((0 : ℝ) : WithBot ℝ) ≤ ((tensionEnergyAt t pitch p) : WithBot ℝ)
    exact WithBot.coe_le_coe.2 hn
  -- `x ⊔ 0 = x` if `0 ≤ x`.
  dsimp [NonnegNucleus.nonnegNucleus, energyWB]
  exact sup_eq_left.2 h0le

theorem helix_energyWB_fixed (t pitch : ℝ) :
    NonnegNucleus.nonnegNucleus.R (energyWB t pitch (helix t pitch)) =
      energyWB t pitch (helix t pitch) := by
  simpa using energyWB_fixed (t := t) (pitch := pitch) (p := helix t pitch)

end SpiralEnergy

end Bridge
end IteratedVirtual
end HeytingLean
