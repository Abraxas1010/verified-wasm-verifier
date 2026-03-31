import HeytingLean.Quantum.QState

namespace HeytingLean.Tests.Quantum

open HeytingLean Quantum

variable {n : ℕ}

example : PosSemidef (0 : Mat n) := PosSemidef.zero

variable (ρ : Density n)

example : ρ.trace = (1 : ℂ) := Density.trace_eq_one ρ
example : ρ.trace.re = 1 := Density.realTrace_eq_one ρ

end HeytingLean.Tests.Quantum

