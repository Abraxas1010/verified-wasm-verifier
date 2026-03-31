import CombinatorialGames.Surreal.Multiplication

namespace HeytingLean
namespace Tests
namespace Numbers

-- Baseline interop checks against the upstream Surreal API surface.
#check Surreal
#check (inferInstance : CommRing Surreal)
#check (inferInstance : IsStrictOrderedRing Surreal)

example : ((0 : Surreal) + 1) = 1 := by
  simp

example : ((1 : Surreal) * 1) = 1 := by
  simp

end Numbers
end Tests
end HeytingLean
