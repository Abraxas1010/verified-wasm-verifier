import HeytingLean.Hyperseries.Category.OmegaTowerLimitGroupoidUniversal

namespace HeytingLean
namespace Tests
namespace Numbers

open CategoryTheory
open HeytingLean.Hyperseries.Category
open HeytingLean.LoF.Combinators.Category (TowerLimit)

#check HGLeftTowerCone
#check HGRightTowerCone
#check liftGLeft
#check liftGRight
#check liftGLeft_fac
#check liftGRight_fac
#check liftGLeft_uniq
#check liftGRight_uniq
#check eqToHom_app_gleft
#check eqToHom_app_gright

example {D : Type} [Category D] (c : HGLeftTowerCone D) (n : Nat) :
    (liftGLeft c) ⋙ TowerLimit.eval n = c.π n := by
  simpa using liftGLeft_fac c n

example {D : Type} [Category D] (c : HGRightTowerCone D) (n : Nat) :
    (liftGRight c) ⋙ TowerLimit.eval n = c.π n := by
  simpa using liftGRight_fac c n

example {X Y : HGOmegaLeft} (hXY : X = Y) (n : Nat) :
    ((eqToHom hXY : X ⟶ Y).app n) =
      eqToHom (congrArg (fun Z : HGOmegaLeft => Z.obj n) hXY) := by
  exact eqToHom_app_gleft hXY n

example {X Y : HGOmegaRight} (hXY : X = Y) (n : Nat) :
    ((eqToHom hXY : X ⟶ Y).app n) =
      eqToHom (congrArg (fun Z : HGOmegaRight => Z.obj n) hXY) := by
  exact eqToHom_app_gright hXY n

end Numbers
end Tests
end HeytingLean
