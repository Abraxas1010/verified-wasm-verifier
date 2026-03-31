import HeytingLean.IteratedVirtual.SpiralStrict22
import HeytingLean.IteratedVirtual.StrictNPresheaf

/-!
# Tests.IteratedVirtual.StrictNPresheafSanity

Compile-only checks that the strict `Catₙ` scaffold can be viewed as a presheaf globular set, and
that a “top cell” can be packaged as a map from the walking globe representable.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

section
  #check StrictNCategory.toPresheaf (n := 22) spiral22Cat
  #check StrictNCategory.CellTopPsh (n := 22) spiral22Cat
  #check StrictNCategory.cellTopPshOf (n := 22) spiral22Cat spiral22Params
end

end IteratedVirtual
end Tests
end HeytingLean

