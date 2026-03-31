import HeytingLean.IteratedVirtual.SpiralStrict22

/-!
# Tests.IteratedVirtual.StrictNSpiralSanity

Compile-only sanity checks for the Phase 6 “true Catₙ” layer:
- `StrictNCategory` (truncated, no `(n+1)` requirement),
- the walking `n`-globe `GlobeN n`,
- and a literal “spiral as a 22-cell” example.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

#check HeytingLean.IteratedVirtual.NGlobularSet
#check HeytingLean.IteratedVirtual.GlobeN
#check HeytingLean.IteratedVirtual.StrictNCategory

-- The spiral 22-category and its canonical 22-cell exist.
#check HeytingLean.IteratedVirtual.spiral22Cat
#check HeytingLean.IteratedVirtual.spiral22Cell

end IteratedVirtual
end Tests
end HeytingLean

