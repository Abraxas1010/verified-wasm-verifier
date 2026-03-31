import Mathlib.CategoryTheory.Comma.Arrow
import HeytingLean.Hyperseries.Category.Groupoid

namespace HeytingLean
namespace Hyperseries
namespace Category

open CategoryTheory

/--
Category package used to define the strict hyperseries Arrow tower recursively.
-/
structure CatPkg where
  Obj : Type _
  inst : CategoryTheory.Category Obj

attribute [instance] CatPkg.inst

/--
Strict Arrow tower based at the hyperseries free-groupoid completion.
-/
def HCatPkg : Nat → CatPkg
  | 0 => { Obj := HExprFreeGroupoid, inst := by infer_instance }
  | Nat.succ n =>
      let C := HCatPkg n
      letI : CategoryTheory.Category C.Obj := C.inst
      { Obj := CategoryTheory.Arrow C.Obj, inst := by infer_instance }

/-- Underlying object type at level `n` of the hyperseries Arrow tower. -/
abbrev HCat (n : Nat) : Type _ := (HCatPkg n).Obj

instance (n : Nat) : CategoryTheory.Category (HCat n) :=
  (HCatPkg n).inst

/-- Source object of an `(n+1)`-cell in the strict Arrow tower. -/
abbrev src {n : Nat} (f : HCat (Nat.succ n)) : HCat n := f.left

/-- Target object of an `(n+1)`-cell in the strict Arrow tower. -/
abbrev tgt {n : Nat} (f : HCat (Nat.succ n)) : HCat n := f.right

/-- Boundary edge of an `(n+1)`-cell in the strict Arrow tower. -/
abbrev edge {n : Nat} (f : HCat (Nat.succ n)) : src f ⟶ tgt f := f.hom

end Category
end Hyperseries
end HeytingLean
