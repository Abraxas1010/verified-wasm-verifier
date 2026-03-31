import HeytingLean.Quantum.QFreeEnergy

namespace HeytingLean.Tests.Quantum

open HeytingLean Quantum

noncomputable section

example (ρ : Density 2) : qRelEnt ρ ρ = 0 := by
  simp

end

end HeytingLean.Tests.Quantum
