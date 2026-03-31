import HeytingLean.Algebra.BarConstruction.Bridge
import HeytingLean.Algebra.SpectralSequence.Bridge

namespace HeytingLean
namespace Bridges
namespace Archetype

theorem bar_to_spectral_trajectory (level : Nat → Nat)
    (h : Topos.JRatchet.RatchetTrajectory level) :
    Topos.JRatchet.RatchetTrajectory
      (fun n =>
        Algebra.SpectralSequence.filtrationLevel
          (fun k => Algebra.BarConstruction.barFiltrationDegree (level k)) n) := by
  intro a b hab
  simpa [Algebra.SpectralSequence.filtrationLevel] using
    Algebra.BarConstruction.ratchet_lifts_to_bar_filtration (level := level) h a b hab

theorem bar_to_spectral_filtration_bridge (level : Nat → Nat)
    (h : Topos.JRatchet.RatchetTrajectory level)
    (a b : Nat) (hab : a ≤ b) :
    Algebra.SpectralSequence.filtrationLevel
      (fun n => Algebra.BarConstruction.barFiltrationDegree (level n)) a ≤
      Algebra.SpectralSequence.filtrationLevel
        (fun n => Algebra.BarConstruction.barFiltrationDegree (level n)) b := by
  exact Algebra.SpectralSequence.ratchet_induces_filtration_monotone
    (level := fun n =>
      Algebra.SpectralSequence.filtrationLevel
        (fun k => Algebra.BarConstruction.barFiltrationDegree (level k)) n)
    (bar_to_spectral_trajectory level h) a b hab

end Archetype
end Bridges
end HeytingLean
