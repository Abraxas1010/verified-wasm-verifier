import HeytingLean.Hyperseries.Category.OmegaTowerLimitUniversal

namespace HeytingLean
namespace Tests
namespace Numbers

open CategoryTheory
open HeytingLean.Hyperseries.Category
open HeytingLean.LoF.Combinators.Category (TowerLimit)

#check HLeftTowerCone
#check HRightTowerCone
#check liftLeft
#check liftRight
#check liftLeft_fac
#check liftRight_fac
#check liftLeft_uniq
#check liftRight_uniq
#check eqToHom_app_left
#check eqToHom_app_right

example {D : Type} [Category D] (c : HLeftTowerCone D) (n : Nat) :
    (liftLeft c) ⋙ TowerLimit.eval n = c.π n := by
  simpa using liftLeft_fac c n

example {D : Type} [Category D] (c : HRightTowerCone D) (n : Nat) :
    (liftRight c) ⋙ TowerLimit.eval n = c.π n := by
  simpa using liftRight_fac c n

example {X Y : HOmegaLeft} (hXY : X = Y) (n : Nat) :
    ((eqToHom hXY : X ⟶ Y).app n) =
      eqToHom (congrArg (fun Z : HOmegaLeft => Z.obj n) hXY) := by
  exact eqToHom_app_left hXY n

example {X Y : HOmegaRight} (hXY : X = Y) (n : Nat) :
    ((eqToHom hXY : X ⟶ Y).app n) =
      eqToHom (congrArg (fun Z : HOmegaRight => Z.obj n) hXY) := by
  exact eqToHom_app_right hXY n

end Numbers
end Tests
end HeytingLean
