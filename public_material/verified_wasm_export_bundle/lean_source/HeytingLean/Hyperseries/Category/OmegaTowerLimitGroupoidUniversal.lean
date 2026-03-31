import HeytingLean.Hyperseries.Category.OmegaTowerLimitGroupoid
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimitUniversal

namespace HeytingLean
namespace Hyperseries
namespace Category

open CategoryTheory
open HeytingLean.LoF.Combinators.Category (TowerCone TowerLimit)

universe u v

/-- A strict cone over the hyperseries left groupoid Arrow tower. -/
abbrev HGLeftTowerCone (D : Type u) [Category.{v} D] : Type _ :=
  TowerCone HGLeftTower D

/-- A strict cone over the hyperseries right groupoid Arrow tower. -/
abbrev HGRightTowerCone (D : Type u) [Category.{v} D] : Type _ :=
  TowerCone HGRightTower D

variable {D : Type u} [Category.{v} D]

/-- Canonical lift of a strict cone into the ω-limit of the hyperseries left groupoid Arrow tower. -/
def liftGLeft (c : HGLeftTowerCone D) : D ⥤ HGOmegaLeft :=
  TowerCone.lift (T := HGLeftTower) c

/-- Canonical lift of a strict cone into the ω-limit of the hyperseries right groupoid Arrow tower. -/
def liftGRight (c : HGRightTowerCone D) : D ⥤ HGOmegaRight :=
  TowerCone.lift (T := HGRightTower) c

/-- `liftGLeft` factors each projection strictly. -/
theorem liftGLeft_fac (c : HGLeftTowerCone D) (n : Nat) :
    (liftGLeft c) ⋙ TowerLimit.eval n = c.π n := by
  simpa [liftGLeft, HGOmegaLeft] using
    (TowerCone.lift_fac (T := HGLeftTower) c n)

/-- `liftGRight` factors each projection strictly. -/
theorem liftGRight_fac (c : HGRightTowerCone D) (n : Nat) :
    (liftGRight c) ⋙ TowerLimit.eval n = c.π n := by
  simpa [liftGRight, HGOmegaRight] using
    (TowerCone.lift_fac (T := HGRightTower) c n)

/-- Uniqueness of the lift into the ω-limit of the hyperseries left groupoid Arrow tower. -/
theorem liftGLeft_uniq (c : HGLeftTowerCone D) (F : D ⥤ HGOmegaLeft)
    (h : ∀ n, F ⋙ TowerLimit.eval n = c.π n) :
    F = liftGLeft c := by
  simpa [liftGLeft, HGOmegaLeft] using
    (TowerCone.lift_uniq (T := HGLeftTower) c F h)

/-- Uniqueness of the lift into the ω-limit of the hyperseries right groupoid Arrow tower. -/
theorem liftGRight_uniq (c : HGRightTowerCone D) (F : D ⥤ HGOmegaRight)
    (h : ∀ n, F ⋙ TowerLimit.eval n = c.π n) :
    F = liftGRight c := by
  simpa [liftGRight, HGOmegaRight] using
    (TowerCone.lift_uniq (T := HGRightTower) c F h)

@[simp] theorem eqToHom_app_gleft {X Y : HGOmegaLeft} (hXY : X = Y) (n : Nat) :
    ((eqToHom hXY : X ⟶ Y).app n) =
      eqToHom (congrArg (fun Z : HGOmegaLeft => Z.obj n) hXY) := by
  exact TowerCone.eqToHom_app (T := HGLeftTower) hXY n

@[simp] theorem eqToHom_app_gright {X Y : HGOmegaRight} (hXY : X = Y) (n : Nat) :
    ((eqToHom hXY : X ⟶ Y).app n) =
      eqToHom (congrArg (fun Z : HGOmegaRight => Z.obj n) hXY) := by
  exact TowerCone.eqToHom_app (T := HGRightTower) hXY n

end Category
end Hyperseries
end HeytingLean
