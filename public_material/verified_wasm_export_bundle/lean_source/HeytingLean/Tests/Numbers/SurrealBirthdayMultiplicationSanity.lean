import HeytingLean.Numbers.Surreal.Birthday.Multiplication

namespace HeytingLean.Tests.Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.Birthday

example : (birthdayMul nullCut (LoFProgram.natPreGame 5)).birth = 0 := by
  simp

example : (birthdayMul (LoFProgram.natPreGame 5) nullCut).birth = 0 := by
  simp

example : (birthdayMul (LoFProgram.natPreGame 0) (LoFProgram.natPreGame 5)).birth = fredman 0 5 := by
  simp

example : (birthdayMul (LoFProgram.natPreGame 5) (LoFProgram.natPreGame 0)).birth = fredman 5 0 := by
  simp

example : (birthdayMul (LoFProgram.natPreGame 2) (LoFProgram.natPreGame 3)).birth ≤ fredman 2 3 := by
  simpa using birthdayMul_natPreGame_birth_le 2 3

example : (birthdayMul (LoFProgram.natPreGame 3) (LoFProgram.natPreGame 3)).birth ≤ 31 := by
  simpa using birthdayMul_natPreGame_birth_le 3 3

end HeytingLean.Tests.Numbers
