import HeytingLean.Eigen.NucleusThreshold

namespace HeytingLean
namespace Eigen
namespace BEACONS

/-!
Flux-limiter-style nucleus: compute a conservative floor from a signal and use
the existing threshold nucleus over `Fin n → ℝ`.

This keeps the operator inside the nucleus discipline (extensive/idempotent/
meet-preserving) while exposing a tunable limiter parameter `κ`.
-/

def fluxFloor (κ : ℝ) {n : Nat} (signal : Fin n → ℝ) : Fin n → ℝ :=
  fun i => -κ * |signal i|

def fluxLimiterNucleus (n : Nat) (κ : ℝ) (signal : Fin n → ℝ) :
    Nucleus (Fin n → ℝ) :=
  thresholdNucleus n (fluxFloor κ signal)

theorem fluxLimiterNucleus_idempotent
    (n : Nat) (κ : ℝ) (signal v : Fin n → ℝ) :
    fluxLimiterNucleus n κ signal (fluxLimiterNucleus n κ signal v) =
      fluxLimiterNucleus n κ signal v := by
  exact thresholdNucleus_idempotent n (fluxFloor κ signal) v

theorem fluxLimiterNucleus_le_apply
    (n : Nat) (κ : ℝ) (signal v : Fin n → ℝ) :
    v ≤ fluxLimiterNucleus n κ signal v := by
  exact thresholdNucleus_le_apply n (fluxFloor κ signal) v

theorem fluxLimiterNucleus_map_inf
    (n : Nat) (κ : ℝ) (signal v w : Fin n → ℝ) :
    fluxLimiterNucleus n κ signal (v ⊓ w : Fin n → ℝ) =
      (fluxLimiterNucleus n κ signal v ⊓ fluxLimiterNucleus n κ signal w : Fin n → ℝ) := by
  exact thresholdNucleus_map_inf n (fluxFloor κ signal) v w

theorem fluxLimiterNucleus_fixed_iff
    (n : Nat) (κ : ℝ) (signal v : Fin n → ℝ) :
    fluxLimiterNucleus n κ signal v = v ↔ fluxFloor κ signal ≤ v := by
  exact thresholdNucleus_fixed_iff n (fluxFloor κ signal) v

end BEACONS
end Eigen
end HeytingLean
