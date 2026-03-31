import HeytingLean.LoF.Combinators.Birthday.DecisionGate

namespace HeytingLean.Tests.LoF

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Birthday

example : (measureSample 4 Comb.I).structuralBirthday = 3 := by
  simp

example : 0 < (measureSample 4 (Comb.app Comb.Y Comb.K)).sourceNodes := by
  simp

example : baselineSamples ≠ [] := by
  simp

end HeytingLean.Tests.LoF
