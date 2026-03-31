import HeytingLean.Bridges.JRatchet

namespace HeytingLean
namespace Tests
namespace Bridges
namespace JRatchetSanity

open HeytingLean.Bridges.JRatchet

/-! Core interface smoke checks. -/
#check RatchetWitness
#check RatchetWitness.const
#check RatchetWitness.identity

/-! Conversion surface smoke checks. -/
#check radialToWitness
#check assemblyToWitness
#check eigenformSoupToWitness
#check constToWitness

/-! RatchetStep ↔ Nucleus parallel smoke checks. -/
#check ratchetStep_extensive
#check ratchetStep_monotone
#check ratchetStep_idempotent
#check ratchetStep_is_nucleus_on_nuclei
#check ratchetStep_apply_is_fixed
#check ratchetTower_converges_at_one

/-! Sheaf glue smoke checks. -/
#check frameLevelCore_iff_ontologicalDriver
#check ontologicalDriver_iff_frameLevelCore
#check radialSpentFuel_is_trajectory
#check jTrajectoryEquiv

/-! Literature extension smoke checks. -/
#check Extensions.PataraiaNuclearJoin.PreRatchetStep
#check Extensions.PataraiaNuclearJoin.ratchetStepJoin
#check Extensions.PreRatchetStabilization.stabilize
#check Extensions.QuanticRatchetStep.QuanticStep
#check Extensions.NuclearRangeRatchet.SemilatticeNucleus
#check Extensions.DiegoFiniteness.NuclearImplicativeSemilattice
#check Extensions.DragalinRatchet.DragalinRatchetWitness
#check Extensions.SpatialityRatchet.NuclearPoint

/-! Registry sanity. -/
example : allJRatchetTags.length = 20 := by
  decide

#eval allJRatchetTags.length

/-! Concrete witness smoke checks. -/

example : (RatchetWitness.const 42).at_ 0 = 42 := rfl
example : (RatchetWitness.const 42).at_ 100 = 42 := rfl

example : (RatchetWitness.identity).at_ 0 = 0 := rfl
example : (RatchetWitness.identity).at_ 5 = 5 := rfl

example : (RatchetWitness.identity).le_of_le (Nat.le_of_lt (Nat.lt.base 3)) =
    Nat.le_of_lt (Nat.lt.base 3) := rfl

/-! ## Cross-variant behavioral coherence -/

/-- Monotonicity holds across witness constructors: const witnesses never decrease. -/
example : ∀ f₁ f₂ : Nat, f₁ ≤ f₂ →
    (RatchetWitness.const 7).at_ f₁ ≤ (RatchetWitness.const 7).at_ f₂ :=
  fun _ _ _ => le_refl 7

/-- Monotonicity holds for identity witness across a range. -/
example : ∀ f₁ f₂ : Nat, f₁ ≤ f₂ →
    (RatchetWitness.identity).at_ f₁ ≤ (RatchetWitness.identity).at_ f₂ :=
  fun _ _ h => h

/-- Witness ordering: const 0 ≤ identity at all fuel values ≥ 0 (trivially). -/
example : (RatchetWitness.const 0).at_ 10 ≤ (RatchetWitness.identity).at_ 10 :=
  Nat.zero_le 10

/-- Witness ordering: const n ≤ identity fails for large constants. -/
example : ¬ ((RatchetWitness.const 100).at_ 5 ≤ (RatchetWitness.identity).at_ 5) := by
  decide

/-- Two witnesses from the same constructor with same data agree pointwise. -/
example : ∀ fuel : Nat,
    (RatchetWitness.const 3).at_ fuel = (RatchetWitness.const 3).at_ fuel :=
  fun _ => rfl

/-- Monotonicity proof term is definitionally what we expect for const. -/
example : (RatchetWitness.const 5).monotone 0 10 (Nat.zero_le 10) = le_refl 5 := rfl

/-- Monotonicity proof term is definitionally what we expect for identity. -/
example : (RatchetWitness.identity).monotone 3 7 (Nat.le_of_lt (Nat.lt.step
    (Nat.lt.step (Nat.lt.step (Nat.lt.base 3))))) =
    Nat.le_of_lt (Nat.lt.step (Nat.lt.step (Nat.lt.step (Nat.lt.base 3)))) := rfl

end JRatchetSanity
end Bridges
end Tests
end HeytingLean
