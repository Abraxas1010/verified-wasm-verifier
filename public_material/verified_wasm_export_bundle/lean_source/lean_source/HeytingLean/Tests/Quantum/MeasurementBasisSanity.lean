import HeytingLean.Quantum.Measurement.Basis

namespace HeytingLean.Tests.Quantum

open HeytingLean Quantum
open scoped BigOperators

variable {n : ℕ} (ρ : Density n)

example (i : Fin n) : 0 ≤ basisProb ρ i :=
  basisProb_nonneg ρ i

example : (∑ i : Fin n, basisProb ρ i) = 1 :=
  basisProb_sum ρ

end HeytingLean.Tests.Quantum

