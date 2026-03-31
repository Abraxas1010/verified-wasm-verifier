import HeytingLean.Algebra.BarConstruction.Basic
import HeytingLean.Algebra.SpectralSequence.Basic
import HeytingLean.Metrics.Magnitude.Basic
import HeytingLean.Topos.JRatchet

namespace HeytingLean
namespace Algebra
namespace BarConstruction

universe u

theorem bar_filtration_ratchet_trajectory (level : Nat → Nat)
    (h : Topos.JRatchet.RatchetTrajectory level) :
    Topos.JRatchet.RatchetTrajectory (fun n => barFiltrationDegree (level n)) := by
  intro a b hab
  exact barFiltrationDegree_monotone (level a) (level b) (h a b hab)

theorem ratchet_lifts_to_bar_filtration (level : Nat → Nat)
    (h : Topos.JRatchet.RatchetTrajectory level)
    (a b : Nat) (hab : a ≤ b) :
    barFiltrationDegree (level a) ≤ barFiltrationDegree (level b) := by
  exact bar_filtration_ratchet_trajectory (level := level) h a b hab

theorem bar_simplex_finiteMagnitude (M : Type u) [Fintype M] (n : Nat) :
    Metrics.Magnitude.finiteMagnitude (BarSimplex M n) =
      Metrics.Magnitude.finiteMagnitude M ^ n := by
  simp [Metrics.Magnitude.finiteMagnitude]

theorem bar_to_spectral_filtration_monotone (level : Nat → Nat)
    (h : Topos.JRatchet.RatchetTrajectory level)
    (a b : Nat) (hab : a ≤ b) :
    SpectralSequence.filtrationLevel (fun n => barFiltrationDegree (level n)) a ≤
      SpectralSequence.filtrationLevel (fun n => barFiltrationDegree (level n)) b := by
  simpa [SpectralSequence.filtrationLevel] using
    bar_filtration_ratchet_trajectory (level := level) h a b hab

end BarConstruction
end Algebra
end HeytingLean
