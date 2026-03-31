import HeytingLean.IteratedVirtual.GlobularPresheaf
import HeytingLean.IteratedVirtual.GlobularRoundTripPsh

/-!
# Tests.IteratedVirtual.GlobularRoundTripPshSanity

Compile-only checks for `GlobularSetPsh.toGlobularSet_toPresheafIso`.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

section
  #check GlobularSetPsh.toGlobularSet_toPresheafIso (X := GlobePsh 3)
end

end IteratedVirtual
end Tests
end HeytingLean
