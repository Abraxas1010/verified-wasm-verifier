import HeytingLean.IteratedVirtual.Equipment
import HeytingLean.IteratedVirtual.IteratedHom
import HeytingLean.IteratedVirtual.Examples.Trivial

/-!
Compile-only sanity checks for the IteratedVirtual MVP scaffold.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

#check HeytingLean.IteratedVirtual.VirtualDoubleCategory
#check HeytingLean.IteratedVirtual.VirtualEquipment

-- The trivial example instantiates the structures.
#check HeytingLean.IteratedVirtual.Examples.trivialEquipment

-- `Cell22` is defined as “length-22 chain” data in any category.
example : HeytingLean.IteratedVirtual.Cell22 (C := Type) :=
  { src := PUnit
    tgt := PUnit
    chain := HeytingLean.IteratedVirtual.VChain.idRep (C := Type) PUnit 22
    length_eq := by simp }

end IteratedVirtual
end Tests
end HeytingLean
