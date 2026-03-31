import HeytingLean.LoF.MRSystems.ReaderTerminal

/-!
Sanity checks for `LoF/MRSystems/ReaderTerminal.lean`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF.MRSystems

universe u

variable (A : Type u)

#check readerUnitCoalgebra (A := A)
#check readerUnitCoalgebra_isTerminal (A := A)

end LoF
end Tests
end HeytingLean

