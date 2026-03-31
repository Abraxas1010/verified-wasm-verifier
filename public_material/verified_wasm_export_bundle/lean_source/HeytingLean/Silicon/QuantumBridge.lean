import Mathlib.Data.Complex.BigOperators
import HeytingLean.Probability.InfoTheory.FinDist
import HeytingLean.Quantum.QState

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

namespace QuantumBridge

/-- Computational-basis measurement of a density matrix as a finite distribution on outcomes `Fin n`. -/
noncomputable def basisMeasurement {n : ℕ} (ρ : HeytingLean.Quantum.Density n) :
    FinDist (Fin n) where
  pmf i := (ρ.mat i i).re
  nonneg i := by
    classical
    -- Positivity follows from positive-semidefiniteness on the basis ket.
    have h := ρ.posSemidef (HeytingLean.Quantum.basisKet (n := n) i)
    simpa using h
  sum_one := by
    classical
    -- Sum of diagonal real parts is the real part of the trace.
    have htrace : (Matrix.trace ρ.mat).re = 1 := by
      simpa using ρ.realTrace_eq_one
    calc
      (∑ i : Fin n, (ρ.mat i i).re)
          = (∑ i : Fin n, ρ.mat i i).re := by
              simp
      _ = (Matrix.trace ρ.mat).re := by
              simp [Matrix.trace]
      _ = 1 := htrace

end QuantumBridge

end

end Silicon
end HeytingLean
