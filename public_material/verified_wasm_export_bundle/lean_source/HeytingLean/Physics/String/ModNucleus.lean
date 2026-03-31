import HeytingLean.Physics.String.Modular

/-
Modular “nucleus” scaffold over finite partitions.
Provides a closure function and a fixed-point predicate.
-/

namespace HeytingLean
namespace Physics
namespace String

open HeytingLean.Physics.String

structure ModNucleus where
  steps : Nat := 8
  closure : Partition → Array Partition := fun Z => HeytingLean.Physics.String.closure Z 8

namespace ModNucleus

@[simp] def fixed (N : ModNucleus) (Z : Partition) : Bool :=
  let orb := N.closure Z
  -- fixed if S and T keep us inside {Z} only
  let sZ := sTransform Z
  let tZ := tTransform Z
  (orb.size = 1) && eqPart sZ Z && eqPart tZ Z

end ModNucleus

end String
end Physics
end HeytingLean
