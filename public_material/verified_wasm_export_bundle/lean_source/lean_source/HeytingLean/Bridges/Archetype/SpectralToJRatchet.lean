import HeytingLean.Algebra.SpectralSequence.Bridge

namespace HeytingLean
namespace Bridges
namespace Archetype

theorem spectral_to_jratchet_filtration (level : Nat → Nat)
    (h : Topos.JRatchet.RatchetTrajectory level)
    (a b : Nat) (hab : a ≤ b) :
    Algebra.SpectralSequence.filtrationLevel level a ≤
      Algebra.SpectralSequence.filtrationLevel level b := by
  exact Algebra.SpectralSequence.ratchet_induces_filtration_monotone level h a b hab

end Archetype
end Bridges
end HeytingLean
