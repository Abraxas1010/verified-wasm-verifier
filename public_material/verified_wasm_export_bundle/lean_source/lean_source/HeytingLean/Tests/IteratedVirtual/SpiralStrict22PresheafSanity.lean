import HeytingLean.IteratedVirtual.SpiralStrict22Presheaf

/-!
# Tests.IteratedVirtual.SpiralStrict22PresheafSanity

Compile-only checks that the spiral 22-cell is exposed as a presheaf globe-map.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

section
  #check SpiralStrict22.spiral22TopCell
  #check SpiralStrict22.spiral22AsGlobeMap
end

end IteratedVirtual
end Tests
end HeytingLean

