import Mathlib.CategoryTheory.Comma.Arrow
import HeytingLean.Hyperseries.Category.NFoldCategoryArrow
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimit

namespace HeytingLean
namespace Hyperseries
namespace Category

open CategoryTheory
open HeytingLean.LoF.Combinators.Category (CatTower TowerLimit)

/-- One-step left boundary projection in the hyperseries Arrow tower. -/
abbrev HDropLeft (n : Nat) : HCat (n + 1) ⥤ HCat n :=
  Arrow.leftFunc (C := HCat n)

/-- One-step right boundary projection in the hyperseries Arrow tower. -/
abbrev HDropRight (n : Nat) : HCat (n + 1) ⥤ HCat n :=
  Arrow.rightFunc (C := HCat n)

/-- Hyperseries strict Arrow tower with left-boundary drop functors. -/
def HLeftTower : CatTower where
  Obj := HCat
  inst := fun n => by infer_instance
  drop := fun n => HDropLeft n

/-- Hyperseries strict Arrow tower with right-boundary drop functors. -/
def HRightTower : CatTower where
  Obj := HCat
  inst := fun n => by infer_instance
  drop := fun n => HDropRight n

/-- ω-limit of the hyperseries left-boundary Arrow tower. -/
abbrev HOmegaLeft : Type _ := TowerLimit HLeftTower

/-- ω-limit of the hyperseries right-boundary Arrow tower. -/
abbrev HOmegaRight : Type _ := TowerLimit HRightTower

end Category
end Hyperseries
end HeytingLean
