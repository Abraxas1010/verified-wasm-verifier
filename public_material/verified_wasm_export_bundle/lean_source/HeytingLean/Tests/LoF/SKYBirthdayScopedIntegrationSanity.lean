import HeytingLean.LoF.Combinators.Birthday.ScopedIntegration

namespace HeytingLean.Tests.LoF

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Birthday
open HeytingLean.LoF.Combinators.SKYUniversality

example : selfProgramBirthday (.base Comb.K) = 1 := by
  rfl

example : selfProgramBirthday (repeatedUnfold Comb.K 3) = 4 := by
  native_decide

end HeytingLean.Tests.LoF
