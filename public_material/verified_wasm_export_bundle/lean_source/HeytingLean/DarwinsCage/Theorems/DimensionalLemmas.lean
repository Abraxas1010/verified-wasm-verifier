import HeytingLean.DarwinsCage.Physics.HighDim

/-!
# Dimensional threshold lemmas

Reusable arithmetic facts about the `aboveDimensionalThreshold` predicate used by
the high-dimensional scenarios.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Theorems

open Physics

variable {L : Type*} [CompleteLattice L]

theorem aboveDimensionalThreshold_iff (rep : PhysicsRepresentation L) (t : ℕ) :
    aboveDimensionalThreshold rep t ↔ representationDim rep > t := Iff.rfl

theorem aboveDimensionalThreshold_succ_le (rep : PhysicsRepresentation L) (t : ℕ) :
    aboveDimensionalThreshold rep t ↔ t.succ ≤ representationDim rep := by
  dsimp [aboveDimensionalThreshold]
  constructor
  · intro ht
    have : t < representationDim rep := by simpa [gt_iff_lt] using ht
    exact (Nat.lt_iff_add_one_le.mp this)
  · intro ht
    have : t + 1 ≤ representationDim rep := by simpa [Nat.succ_eq_add_one] using ht
    have : t < representationDim rep := Nat.lt_iff_add_one_le.mpr this
    simpa [gt_iff_lt] using this

theorem aboveDimensionalThreshold_30 (rep : PhysicsRepresentation L) :
    aboveDimensionalThreshold rep 30 ↔ 31 ≤ representationDim rep := by
  exact aboveDimensionalThreshold_succ_le (rep := rep) (t := 30)

theorem aboveDimensionalThreshold_mono (rep : PhysicsRepresentation L) {t₁ t₂ : ℕ}
    (h : t₁ ≤ t₂) :
    aboveDimensionalThreshold rep t₂ → aboveDimensionalThreshold rep t₁ := by
  dsimp [aboveDimensionalThreshold]
  intro ht₂
  exact lt_of_le_of_lt h ht₂

end Theorems
end DarwinsCage
end HeytingLean
