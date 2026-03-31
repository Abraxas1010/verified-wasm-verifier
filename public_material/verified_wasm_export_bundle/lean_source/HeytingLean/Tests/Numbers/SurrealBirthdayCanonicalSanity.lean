import HeytingLean.Numbers.Surreal.Birthday.CanonicalDyadic
import HeytingLean.Numbers.Surreal.Birthday.Negation

namespace HeytingLean.Tests.Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.Surreal.Birthday

example : normalizedBirthday (LoFProgram.natPreGame 3) = 3 := by
  simp

example : normalizedBirthday (LoFProgram.dyadicPreGame 1 1) = 2 := by
  exact normalizedBirthday_oneHalf

example : normalizedBirthday (LoFProgram.intPreGame (-3)) = 3 := by
  simpa using normalizedBirthday_intPreGame (-3 : Int)

example : normalizedBirthday (LoFProgram.intPreGame (-3)) =
    normalizedBirthday (LoFProgram.intPreGame 3) := by
  simpa using normalizedBirthday_intPreGame_neg 3

end HeytingLean.Tests.Numbers
