import HeytingLean.Algebra.SpectralSequence.Basic
import HeytingLean.Topos.JRatchet

namespace HeytingLean
namespace Algebra
namespace SpectralSequence

theorem ratchet_induces_filtration_monotone (level : Nat → Nat)
    (h : Topos.JRatchet.RatchetTrajectory level)
    (a b : Nat) (hab : a ≤ b) :
    filtrationLevel level a ≤ filtrationLevel level b :=
  h a b hab

theorem boundary_cycle_bridge (C : DifferentialComplex) (n : Nat) {x : C.E (n + 1)}
    (hx : IsBoundary C n x) :
    IsCycle C n x :=
  boundary_is_cycle C n hx

end SpectralSequence
end Algebra
end HeytingLean
