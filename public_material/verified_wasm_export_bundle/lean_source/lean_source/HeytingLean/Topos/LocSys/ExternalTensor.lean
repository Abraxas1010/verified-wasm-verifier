import HeytingLean.Topos.LocSys.Grothendieck

import Mathlib.CategoryTheory.Products.Basic

namespace HeytingLean
namespace Topos
namespace LocSys

open CategoryTheory
open scoped MonoidalCategory

universe uK uB vB

variable (K : Type uK) [CommRing K]

namespace LocalSystems

variable {K : Type uK} [CommRing K]
variable {X Y : Grpd.{vB, uB}}

/-- External tensor product of local systems, living over the product base `X×Y`. -/
noncomputable def externalTensor (V : LocalSystem (K := K) X) (W : LocalSystem (K := K) Y) :
    LocalSystem (K := K) (Base1.prod X Y) :=
  (pullback (K := K) (CategoryTheory.Prod.fst X Y)).obj V ⊗ (pullback (K := K) (CategoryTheory.Prod.snd X Y)).obj W

notation:70 V " ⊠[" K "] " W => externalTensor (K := K) V W

@[simp]
theorem externalTensor_obj (V : LocalSystem (K := K) X) (W : LocalSystem (K := K) Y) (x : X) (y : Y) :
    ((externalTensor (K := K) V W).obj (x, y)) = (V.obj x ⊗ W.obj y) :=
  rfl

end LocalSystems

namespace Loc

variable {K}

/-- External tensor on the total category `Loc K` (object-level construction). -/
noncomputable def externalTensorObj {X Y : Loc (K := K)} : Loc (K := K) where
  base := Base1.prod X.base Y.base
  sys := (LocalSystems.externalTensor (K := K) X.sys Y.sys)

/-- External tensor on morphisms in `Loc K`. -/
noncomputable def externalTensorHom {X X' Y Y' : Loc (K := K)} (f : X ⟶ X') (g : Y ⟶ Y') :
    externalTensorObj (K := K) (X := X) (Y := Y) ⟶ externalTensorObj (K := K) (X := X') (Y := Y') where
  base := Functor.prod f.base g.base
  fiber := by
    let fst : Base1.prod X.base Y.base ⥤ X.base := CategoryTheory.Prod.fst X.base Y.base
    let snd : Base1.prod X.base Y.base ⥤ Y.base := CategoryTheory.Prod.snd X.base Y.base
    let α :
        (LocalSystems.pullback (K := K) fst).obj X.sys ⟶
          (LocalSystems.pullback (K := K) fst).obj ((LocalSystems.pullback (K := K) f.base).obj X'.sys) :=
      Functor.whiskerLeft fst f.fiber
    let β :
        (LocalSystems.pullback (K := K) snd).obj Y.sys ⟶
          (LocalSystems.pullback (K := K) snd).obj ((LocalSystems.pullback (K := K) g.base).obj Y'.sys) :=
      Functor.whiskerLeft snd g.fiber
    simpa [LocalSystems.externalTensor, fst, snd, α, β] using (α ⊗ₘ β)

  /-- External tensor as a bifunctor `Loc K × Loc K ⥤ Loc K`. -/
  noncomputable def externalTensor :
      (Loc.{uK, uB, vB} (K := K) × Loc.{uK, uB, vB} (K := K)) ⥤ Loc.{uK, uB, vB} (K := K) where
    obj P := externalTensorObj (K := K) (X := P.1) (Y := P.2)
    map {P Q} f := externalTensorHom (K := K) (X := P.1) (X' := Q.1) (Y := P.2) (Y' := Q.2) f.1 f.2
    map_id P := by
      refine Loc.hom_ext (K := K) _ _ rfl ?_
      refine heq_of_eq ?_
      ext p
      simp [externalTensorHom, externalTensorObj, LocalSystems.externalTensor, LocalSystems.pullback]
    map_comp {P Q R} f g := by
      refine Loc.hom_ext (K := K) _ _ rfl ?_
      refine heq_of_eq ?_
      ext p
      simp [externalTensorHom, externalTensorObj, LocalSystems.externalTensor, LocalSystems.pullback]

  end Loc

end LocSys
end Topos
end HeytingLean
