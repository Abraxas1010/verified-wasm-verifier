import HeytingLean.LoF.Combinators.Birthday.Metric

namespace HeytingLean.Tests.LoF

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Birthday

example : combBirthday Comb.K = 1 := by
  rfl

example : combBirthday Comb.I = 3 := by
  simp

example : 0 < combNodeCount (Comb.app Comb.S Comb.K) := by
  simp

end HeytingLean.Tests.LoF
