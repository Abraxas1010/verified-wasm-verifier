import Mathlib.CategoryTheory.Types.Basic
import HeytingLean.IteratedVirtual.Equipment

/-!
# IteratedVirtual.Examples.Trivial

A tiny instantiation of the MVP API: horizontal proarrows and cells are all `PUnit`.
This is not mathematically interesting; it exists to validate that the structures are
definable and can be instantiated without proof placeholders.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Examples

universe u

/-- The trivial virtual equipment on `Type u`. -/
def trivialEquipment : VirtualEquipment where
  Obj := Type u
  vertCat := by infer_instance
  Horiz := fun _ _ => PUnit
  Cell := fun {_n} _A _B _v _h _tgt => PUnit
  horizId := fun _ => PUnit.unit
  companion := fun {_ _} _ => PUnit.unit
  conjoint := fun {_ _} _ => PUnit.unit
  companionUnit := fun {_ _} _ => PUnit.unit
  companionCounit := fun {_ _} _ => PUnit.unit
  conjointUnit := fun {_ _} _ => PUnit.unit
  conjointCounit := fun {_ _} _ => PUnit.unit

end Examples
end IteratedVirtual
end HeytingLean
