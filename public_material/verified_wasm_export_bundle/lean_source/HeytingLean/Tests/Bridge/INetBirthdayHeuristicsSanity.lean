import HeytingLean.Bridge.INet.Birthday.Heuristics

namespace HeytingLean.Tests.Bridge

open HeytingLean.LoF
open HeytingLean.Bridge.INet.Birthday

example : inetStructuralLoad Comb.K = 1 := by
  simp

example : inetStructuralLoad Comb.S = 1 := by
  simp

example : inetStructuralLoad Comb.Y = 1 := by
  simp

end HeytingLean.Tests.Bridge
