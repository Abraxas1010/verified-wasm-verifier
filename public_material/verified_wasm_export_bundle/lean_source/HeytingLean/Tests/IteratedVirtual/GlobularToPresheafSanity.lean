import HeytingLean.IteratedVirtual.GlobularToPresheaf
import HeytingLean.IteratedVirtual.GlobularFromPresheaf

/-!
# Tests.IteratedVirtual.GlobularToPresheafSanity

Compile-only checks for the `GlobularSet ↔ GlobularSetPsh` conversion helpers.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

section
  variable (X : GlobularSet)
  #check X.toPresheaf
  #check (X.toPresheaf).toGlobularSet
end

end IteratedVirtual
end Tests
end HeytingLean

