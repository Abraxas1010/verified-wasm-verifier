import Mathlib.CategoryTheory.Types.Basic
import HeytingLean.IteratedVirtual.Equipment
import HeytingLean.VETT.Rel.Basic

/-!
# VETT.Rel.IteratedVirtualModel

An explicit `IteratedVirtual.VirtualEquipment` instance whose proarrows are
`Prop`-valued relations. This connects the Phase-10 VETT work to the existing
IteratedVirtual API surface (and the Phase-8 `PastingFramedEval` semantics interface).

This is the virtual equipment of *profunctors between discrete categories*.
-/

namespace HeytingLean.VETT.Rel

open CategoryTheory
open HeytingLean.IteratedVirtual

universe u

namespace RelEquipment

/-- The underlying proarrow type: relations. -/
abbrev Horiz (A B : Type u) : Type u := HRel A B

def horizId (A : Type u) : Horiz A A :=
  RelOps.unit A

def companion {A B : Type u} (f : A ⟶ B) : Horiz A B :=
  fun a b => f a = b

def conjoint {A B : Type u} (f : A ⟶ B) : Horiz B A :=
  fun b a => f a = b

/-- The relation-based virtual equipment (for the IteratedVirtual layer). -/
def equipment : IteratedVirtual.VirtualEquipment where
  Obj := Type u
  vertCat := by infer_instance
  Horiz := Horiz
  Cell := fun {_n} _A _B _v _h _tgt => PUnit
  horizId := horizId
  companion := fun {A B} f => companion f
  conjoint := fun {A B} f => conjoint f
  companionUnit := fun {_A _B} _f => PUnit.unit
  companionCounit := fun {_A _B} _f => PUnit.unit
  conjointUnit := fun {_A _B} _f => PUnit.unit
  conjointCounit := fun {_A _B} _f => PUnit.unit

end RelEquipment
end HeytingLean.VETT.Rel
