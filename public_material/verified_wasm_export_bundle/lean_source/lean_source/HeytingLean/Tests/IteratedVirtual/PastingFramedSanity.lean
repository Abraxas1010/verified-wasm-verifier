import HeytingLean.IteratedVirtual.PastingFramed

/-!
# Tests.IteratedVirtual.PastingFramedSanity

Compile-only checks for the non-identity-framed pasting syntax.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

universe u v w

variable (V : VirtualDoubleCategory.{u, v, w})

section
  #check PastingFramed (V := V)
  #check PastingFramed.bind (V := V)
  #check PastingFramed.bind_pure_right (V := V)
  #check PastingFramed.bind_assoc (V := V)
end

end IteratedVirtual
end Tests
end HeytingLean

