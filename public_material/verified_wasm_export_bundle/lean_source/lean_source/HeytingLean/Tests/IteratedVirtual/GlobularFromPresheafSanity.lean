import HeytingLean.IteratedVirtual.GlobularFromPresheaf

/-!
# Tests.IteratedVirtual.GlobularFromPresheafSanity

Compile-only checks that presheaf globular sets can be viewed as structured `GlobularSet`s.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

section
  variable (n : Nat)
  -- The walking globe presheaf exists.
  #check GlobePsh n
  -- It can be viewed as a structured globular set.
  #check (GlobePsh n).toGlobularSet
end

end IteratedVirtual
end Tests
end HeytingLean

