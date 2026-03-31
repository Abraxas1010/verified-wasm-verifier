import Mathlib.CategoryTheory.Groupoid
import HeytingLean.Hyperseries.Category.OmegaTowerLimit
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimitGroupoid

namespace HeytingLean
namespace Hyperseries
namespace Category

open CategoryTheory
open HeytingLean.LoF.Combinators.Category (CatTower TowerLimit)

/--
Groupoid package used to define the hyperseries Arrow tower recursively.
-/
structure GroupoidPkg where
  Obj : Type _
  inst : Groupoid Obj

attribute [instance] GroupoidPkg.inst

/--
Strict Arrow tower of groupoids starting from `HExprFreeGroupoid`.
-/
noncomputable def HGCatPkg : Nat → GroupoidPkg
  | 0 => { Obj := HExprFreeGroupoid, inst := by infer_instance }
  | Nat.succ n =>
      let C := HGCatPkg n
      letI : Groupoid C.Obj := C.inst
      { Obj := Arrow C.Obj, inst := by infer_instance }

/-- Underlying object type at level `n` of the hyperseries groupoid Arrow tower. -/
abbrev HGCat (n : Nat) : Type _ := (HGCatPkg n).Obj

noncomputable instance (n : Nat) : Groupoid (HGCat n) :=
  (HGCatPkg n).inst

/-- One-step left boundary projection in the hyperseries groupoid Arrow tower. -/
noncomputable abbrev HGDropLeft (n : Nat) : HGCat (n + 1) ⥤ HGCat n :=
  Arrow.leftFunc (C := HGCat n)

/-- One-step right boundary projection in the hyperseries groupoid Arrow tower. -/
noncomputable abbrev HGDropRight (n : Nat) : HGCat (n + 1) ⥤ HGCat n :=
  Arrow.rightFunc (C := HGCat n)

/-- Groupoid-valued hyperseries Arrow tower using left-boundary drop functors. -/
noncomputable def HGLeftTower : CatTower where
  Obj := HGCat
  inst := fun n => by infer_instance
  drop := fun n => HGDropLeft n

/-- Groupoid-valued hyperseries Arrow tower using right-boundary drop functors. -/
noncomputable def HGRightTower : CatTower where
  Obj := HGCat
  inst := fun n => by infer_instance
  drop := fun n => HGDropRight n

/-- ω-limit of the left-boundary hyperseries groupoid tower. -/
abbrev HGOmegaLeft : Type _ := TowerLimit HGLeftTower

/-- ω-limit of the right-boundary hyperseries groupoid tower. -/
abbrev HGOmegaRight : Type _ := TowerLimit HGRightTower

noncomputable instance : Groupoid HGOmegaLeft := by
  dsimp [HGOmegaLeft]
  infer_instance

noncomputable instance : Groupoid HGOmegaRight := by
  dsimp [HGOmegaRight]
  infer_instance

end Category
end Hyperseries
end HeytingLean
