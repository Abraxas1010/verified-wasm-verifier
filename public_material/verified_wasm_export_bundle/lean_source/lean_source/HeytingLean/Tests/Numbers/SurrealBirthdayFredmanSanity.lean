import HeytingLean.Numbers.Surreal.Birthday.Fredman

namespace HeytingLean.Tests.Numbers

open HeytingLean.Numbers.Surreal.Birthday

example : fredman 2 2 = 6 := by
  simp

example : fredman 2 3 = 12 := by
  simp

example : fredman 3 3 = 31 := by
  simp

example : fredman 2 3 = fredman 3 2 := by
  simp [fredman_symm]

end HeytingLean.Tests.Numbers
