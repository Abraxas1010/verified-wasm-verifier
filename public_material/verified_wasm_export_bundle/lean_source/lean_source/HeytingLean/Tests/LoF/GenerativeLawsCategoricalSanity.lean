import HeytingLean.LoF.Axioms.GenerativeLaws

/-!
Sanity checks for `LoF/Axioms/GenerativeLaws.lean`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Axioms.GenerativeLaws

universe u

variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α) (a : α)

#check omegaReflector (R := R)
#check omegaInclusion (R := R)
#check omegaAdjunction (R := R)

#check psr_iff_unit_isIso (R := R) (a := a)
#check reflector_le_iff (R := R) (a := a)
#check close_le_of_le_fixed (R := R)
#check dialectic_least (R := R)

end LoF
end Tests
end HeytingLean

