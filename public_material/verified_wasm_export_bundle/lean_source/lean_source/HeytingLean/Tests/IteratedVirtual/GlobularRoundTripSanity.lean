import HeytingLean.IteratedVirtual.Globe
import HeytingLean.IteratedVirtual.GlobularRoundTrip

/-!
# Tests.IteratedVirtual.GlobularRoundTripSanity

Compile-only checks for the structured→presheaf→structured round-trip isomorphism.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

section
  #check GlobularSet.toPresheaf_toGlobularSetIso (X := Globe 3)
end

end IteratedVirtual
end Tests
end HeytingLean

