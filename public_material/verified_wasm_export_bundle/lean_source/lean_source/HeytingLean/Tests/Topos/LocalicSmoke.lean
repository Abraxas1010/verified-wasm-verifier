import HeytingLean.Topos.Localic

/-!
Localic smoke test (compile-only).

This file is not part of the default topos_tests CLI aggregation to
avoid adding heavy dependencies to the happy path. It ensures that our
`Localic` module imports and type-level checks remain valid.
-/

namespace HeytingLean
namespace Tests
namespace Topos

open CategoryTheory

section
  universe u
  variable (X : Type u) [TopologicalSpace X]
  #check TopCat
  #check HeytingLean.Topos.Localic
end

end Topos
end Tests
end HeytingLean

