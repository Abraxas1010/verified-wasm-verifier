import HeytingLean.Topos.JRatchet

/-!
# JRatchetCore: abstract ratchet witness interface

Every J-ratchet variant produces a `RatchetTrajectory` — a monotone
`Nat → Nat` function witnessing irreversible progression. This module
provides a uniform witness structure and collects the existing
trajectory witnesses under a single umbrella.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet

open HeytingLean.Topos.JRatchet

/-- A ratchet witness bundles a level function with its monotonicity proof.
    Variants with an explicit `Nat → Nat` trajectory can produce one via
    `Conversions.lean`; higher-order variants (RatchetStep on nuclei) use
    the structural parallel in `RatchetStepNucleus.lean` instead. -/
structure RatchetWitness where
  level : Nat → Nat
  monotone : RatchetTrajectory level

namespace RatchetWitness

/-- Level at a given fuel step. -/
def at_ (w : RatchetWitness) (fuel : Nat) : Nat := w.level fuel

/-- The level can only increase. -/
theorem le_of_le (w : RatchetWitness) {fuel₁ fuel₂ : Nat} (h : fuel₁ ≤ fuel₂) :
    w.at_ fuel₁ ≤ w.at_ fuel₂ :=
  w.monotone fuel₁ fuel₂ h

/-- A constant trajectory is a (trivial) ratchet witness. -/
def const (n : Nat) : RatchetWitness where
  level := fun _ => n
  monotone := fun _ _ _ => le_refl n

/-- The identity trajectory `fuel ↦ fuel` is a ratchet witness. -/
def identity : RatchetWitness where
  level := id
  monotone := fun _ _ h => h

end RatchetWitness

end JRatchet
end Bridges
end HeytingLean
