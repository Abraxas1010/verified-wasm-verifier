import HeytingLean.Hyperseries.Category.OmegaTowerLimit
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimitUniversal

namespace HeytingLean
namespace Hyperseries
namespace Category

open CategoryTheory
open HeytingLean.LoF.Combinators.Category (TowerCone TowerLimit)

universe u v

/-- A strict cone over the hyperseries left Arrow tower. -/
abbrev HLeftTowerCone (D : Type u) [Category.{v} D] : Type _ :=
  TowerCone HLeftTower D

/-- A strict cone over the hyperseries right Arrow tower. -/
abbrev HRightTowerCone (D : Type u) [Category.{v} D] : Type _ :=
  TowerCone HRightTower D

variable {D : Type u} [Category.{v} D]

/-- Canonical lift of a strict cone into the ω-limit of the hyperseries left Arrow tower. -/
def liftLeft (c : HLeftTowerCone D) : D ⥤ HOmegaLeft :=
  TowerCone.lift (T := HLeftTower) c

/-- Canonical lift of a strict cone into the ω-limit of the hyperseries right Arrow tower. -/
def liftRight (c : HRightTowerCone D) : D ⥤ HOmegaRight :=
  TowerCone.lift (T := HRightTower) c

/-- `liftLeft` factors each projection strictly. -/
theorem liftLeft_fac (c : HLeftTowerCone D) (n : Nat) :
    (liftLeft c) ⋙ TowerLimit.eval n = c.π n := by
  simpa [liftLeft, HOmegaLeft] using
    (TowerCone.lift_fac (T := HLeftTower) c n)

/-- `liftRight` factors each projection strictly. -/
theorem liftRight_fac (c : HRightTowerCone D) (n : Nat) :
    (liftRight c) ⋙ TowerLimit.eval n = c.π n := by
  simpa [liftRight, HOmegaRight] using
    (TowerCone.lift_fac (T := HRightTower) c n)

/-- Uniqueness of the lift into the ω-limit of the hyperseries left Arrow tower. -/
theorem liftLeft_uniq (c : HLeftTowerCone D) (F : D ⥤ HOmegaLeft)
    (h : ∀ n, F ⋙ TowerLimit.eval n = c.π n) :
    F = liftLeft c := by
  simpa [liftLeft, HOmegaLeft] using
    (TowerCone.lift_uniq (T := HLeftTower) c F h)

/-- Uniqueness of the lift into the ω-limit of the hyperseries right Arrow tower. -/
theorem liftRight_uniq (c : HRightTowerCone D) (F : D ⥤ HOmegaRight)
    (h : ∀ n, F ⋙ TowerLimit.eval n = c.π n) :
    F = liftRight c := by
  simpa [liftRight, HOmegaRight] using
    (TowerCone.lift_uniq (T := HRightTower) c F h)

@[simp] theorem eqToHom_app_left {X Y : HOmegaLeft} (hXY : X = Y) (n : Nat) :
    ((eqToHom hXY : X ⟶ Y).app n) =
      eqToHom (congrArg (fun Z : HOmegaLeft => Z.obj n) hXY) := by
  exact TowerCone.eqToHom_app (T := HLeftTower) hXY n

@[simp] theorem eqToHom_app_right {X Y : HOmegaRight} (hXY : X = Y) (n : Nat) :
    ((eqToHom hXY : X ⟶ Y).app n) =
      eqToHom (congrArg (fun Z : HOmegaRight => Z.obj n) hXY) := by
  exact TowerCone.eqToHom_app (T := HRightTower) hXY n

end Category
end Hyperseries
end HeytingLean
