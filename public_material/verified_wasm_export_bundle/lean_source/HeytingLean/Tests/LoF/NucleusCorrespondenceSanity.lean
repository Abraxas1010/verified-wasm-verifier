import HeytingLean.LoF.Correspondence.NucleusCorrespondence

/-!
Compile-only sanity checks for the nucleus correspondence bridge (`J.close` as a nucleus).
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF.Correspondence

universe v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (X : C)

#check Grothendieck.FixedSieve (C := C) J X
#check Grothendieck.range_eq_fixedPoints (C := C) (J := J) X
#check Grothendieck.closedSieveEquivFixedSieve (C := C) (J := J) X
#check Grothendieck.fixedSieveEquivIsClosed (C := C) (J := J) X
#check Grothendieck.closedSieveEquivIsClosed_viaFixed (C := C) (J := J) X

end LoF
end Tests
end HeytingLean

