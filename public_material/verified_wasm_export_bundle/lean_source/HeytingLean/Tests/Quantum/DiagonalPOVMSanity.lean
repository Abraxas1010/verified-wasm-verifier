import HeytingLean.Quantum.Measurement.DiagonalPOVM

namespace HeytingLean.Tests.Quantum

open HeytingLean Quantum
open scoped BigOperators

variable {n : ℕ}

private noncomputable def basisDiagonalPOVM : Quantum.DiagonalPOVM (n := n) (Fin n) where
  weight x i := if x = i then 1 else 0
  weight_nonneg := by
    intro x i
    by_cases h : x = i <;> simp [h]
  weight_sum_one := by
    intro i
    classical
    simp

example (ρ : Density n) (i : Fin n) :
    (basisDiagonalPOVM (n := n)).prob ρ i = basisProb ρ i := by
  classical
  simp [Quantum.DiagonalPOVM.prob_eq_sum, basisDiagonalPOVM, basisProb]

example (ρ : Density n) : (∑ i : Fin n, (basisDiagonalPOVM (n := n)).prob ρ i) = 1 := by
  classical
  simpa using (Quantum.DiagonalPOVM.prob_sum (Λ := basisDiagonalPOVM (n := n)) ρ)

end HeytingLean.Tests.Quantum

