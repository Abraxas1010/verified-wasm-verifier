import HeytingLean.IteratedVirtual.GlobeCatEquivalence

/-!
# Tests.IteratedVirtual.GlobeCatEquivalenceSanity

Compile-only checks that the presented globe category is equivalent to `GlobularIndex`, and that
presheaf globular semantics can be rebased.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

section
  #check GlobeCatEquivalence.globeCatEquivalence
  #check GlobeCatEquivalence.globularPresheafRebase
end

end IteratedVirtual
end Tests
end HeytingLean

