import HeytingLean.Numbers.Surreal.Birthday.Addition

namespace HeytingLean.Tests.Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.Birthday

example : (birthdayAdd (LoFProgram.natPreGame 2) (LoFProgram.natPreGame 3)).birth = 5 := by
  simp

example : (birthdayAdd nullCut (LoFProgram.natPreGame 4)).birth = 4 := by
  simp

example : (birthdayAdd (LoFProgram.natPreGame 4) nullCut).birth = 4 := by
  simp

end HeytingLean.Tests.Numbers
