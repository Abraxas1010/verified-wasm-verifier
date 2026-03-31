import HeytingLean.Quantum.Density

namespace HeytingLean.Tests.Quantum

open HeytingLean Quantum

variable {n : ℕ}

example (ρ : Density n) : ρ.trace = (1 : ℂ) := Density.trace_eq_one ρ

example : KrausChannel 1 1 := KrausChannel.id 1

end HeytingLean.Tests.Quantum

