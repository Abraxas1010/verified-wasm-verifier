import HeytingLean.LoF.MRSystems.MooreTerminal

/-!
Sanity checks for `LoF/MRSystems/MooreTerminal.lean`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF.MRSystems

universe u

variable (A B : Type u)

#check MooreEndo (A := A) (B := B)
#check mooreFinalCoalgebra (A := A) (B := B)
#check mooreFinalCoalgebra_isTerminal (A := A) (B := B)

end LoF
end Tests
end HeytingLean

