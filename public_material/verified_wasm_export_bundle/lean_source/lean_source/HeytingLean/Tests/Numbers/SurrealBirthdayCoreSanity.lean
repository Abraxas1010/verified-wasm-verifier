import HeytingLean.Numbers.Surreal.Birthday.Core

namespace HeytingLean.Tests.Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.Birthday

example : normalizedBirthday nullCut = 0 := by
  exact normalizedBirthday_nullCut

example (g : BirthdayForm) : parents (PreGame.build [g] []) = [g] := by
  rfl

end HeytingLean.Tests.Numbers
