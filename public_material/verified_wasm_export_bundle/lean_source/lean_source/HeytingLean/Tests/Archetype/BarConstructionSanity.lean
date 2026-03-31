import HeytingLean.Algebra.BarConstruction.README
import HeytingLean.Bridges.Archetype.BarToSpectral

example :
    HeytingLean.Algebra.BarConstruction.barFiltrationDegree 4 = 4 := by
  native_decide

example (M : Type) [Fintype M] (n : Nat) :
    HeytingLean.Metrics.Magnitude.finiteMagnitude (HeytingLean.Algebra.BarConstruction.BarSimplex M n) =
      HeytingLean.Metrics.Magnitude.finiteMagnitude M ^ n := by
  exact HeytingLean.Algebra.BarConstruction.bar_simplex_finiteMagnitude M n

example (n : Nat) :
    HeytingLean.Algebra.SpectralSequence.filtrationLevel
      (fun k => HeytingLean.Algebra.BarConstruction.barFiltrationDegree (k + n)) n ≤
      HeytingLean.Algebra.SpectralSequence.filtrationLevel
        (fun k => HeytingLean.Algebra.BarConstruction.barFiltrationDegree (k + n)) (n + 1) := by
  have htraj : HeytingLean.Topos.JRatchet.RatchetTrajectory (fun k => k + n) := by
    intro a b hab
    exact Nat.add_le_add_right hab n
  exact HeytingLean.Algebra.BarConstruction.bar_to_spectral_filtration_monotone
    (fun k => k + n) htraj n (n + 1) (Nat.le_succ n)

example (n : Nat) :
    HeytingLean.Algebra.SpectralSequence.filtrationLevel
      (fun k => HeytingLean.Algebra.BarConstruction.barFiltrationDegree (k + n)) n ≤
      HeytingLean.Algebra.SpectralSequence.filtrationLevel
        (fun k => HeytingLean.Algebra.BarConstruction.barFiltrationDegree (k + n)) (n + 1) := by
  have htraj : HeytingLean.Topos.JRatchet.RatchetTrajectory (fun k => k + n) := by
    intro a b hab
    exact Nat.add_le_add_right hab n
  exact HeytingLean.Bridges.Archetype.bar_to_spectral_filtration_bridge
    (fun k => k + n) htraj n (n + 1) (Nat.le_succ n)
