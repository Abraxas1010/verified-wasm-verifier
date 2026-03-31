import HeytingLean.Numbers.Surreal.JClosure

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

/-! Compile-only smoke tests for the J-closure core. -/

-- J is extensive and idempotent
example (S : Set PreGame) : S ⊆ HeytingLean.Numbers.Surreal.Core.J S := by
  exact HeytingLean.Numbers.Surreal.Core.subset_J S

example (S : Set PreGame) :
    HeytingLean.Numbers.Surreal.Core.J (HeytingLean.Numbers.Surreal.Core.J S)
      = HeytingLean.Numbers.Surreal.Core.J S := by
  simpa using HeytingLean.Numbers.Surreal.Core.idem_J S

-- Monotone
example (S T : Set PreGame) (hST : S ⊆ T) :
    HeytingLean.Numbers.Surreal.Core.J S
      ⊆ HeytingLean.Numbers.Surreal.Core.J T := by
  exact HeytingLean.Numbers.Surreal.Core.mono_J hST


end Numbers
end Tests
end HeytingLean
