import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimit

namespace HeytingLean
namespace Algebra
namespace HomotopyTower

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

universe u v

attribute [local simp] eqToHom_map

/-- A strict levelwise functor between towers. The drop squares commute on-the-nose. -/
structure TowerFunctor (T U : CatTower.{u, v}) where
  F : ∀ n, T.Obj n ⥤ U.Obj n
  comm : ∀ n, F (n + 1) ⋙ U.drop n = T.drop n ⋙ F n

namespace TowerFunctor

variable {T U V : CatTower.{u, v}}

/-- The identity tower functor. -/
def id (T : CatTower.{u, v}) : TowerFunctor T T where
  F := fun _ => 𝟭 _
  comm := by
    intro n
    rw [Functor.id_comp, Functor.comp_id]

/-- Composition of strict tower functors. -/
def comp (G : TowerFunctor U V) (F : TowerFunctor T U) : TowerFunctor T V where
  F := fun n => F.F n ⋙ G.F n
  comm := by
    intro n
    calc
      (F.F (n + 1) ⋙ G.F (n + 1)) ⋙ V.drop n
          = F.F (n + 1) ⋙ (G.F (n + 1) ⋙ V.drop n) := by rfl
      _ = F.F (n + 1) ⋙ (U.drop n ⋙ G.F n) := by rw [G.comm n]
      _ = (F.F (n + 1) ⋙ U.drop n) ⋙ G.F n := by rfl
      _ = (T.drop n ⋙ F.F n) ⋙ G.F n := by rw [F.comm n]
      _ = T.drop n ⋙ (F.F n ⋙ G.F n) := by rfl

/-- Object-level action of a strict tower functor on a compatible tower point. -/
def mapObj (F : TowerFunctor T U) (X : TowerLimit T) : TowerLimit U where
  obj := fun n => (F.F n).obj (X.obj n)
  compat := by
    intro n
    exact
      (Functor.congr_obj (F.comm n) (X.obj (n + 1))).trans
        (congrArg (fun Z => (F.F n).obj Z) (X.compat n))

/-- The induced functor on inverse-limit categories. -/
def mapLimit (F : TowerFunctor T U) : TowerLimit T ⥤ TowerLimit U where
  obj := mapObj F
  map {X Y} f :=
    { app := fun n => (F.F n).map (f.app n)
      comm := by
        intro n
        let hX₁ :
            (U.drop n).obj ((F.F (n + 1)).obj (X.obj (n + 1))) =
              (F.F n).obj ((T.drop n).obj (X.obj (n + 1))) :=
          Functor.congr_obj (F.comm n) (X.obj (n + 1))
        let hX₂ :
            (F.F n).obj ((T.drop n).obj (X.obj (n + 1))) = (F.F n).obj (X.obj n) :=
          congrArg (fun Z => (F.F n).obj Z) (X.compat n)
        let hY₁ :
            (U.drop n).obj ((F.F (n + 1)).obj (Y.obj (n + 1))) =
              (F.F n).obj ((T.drop n).obj (Y.obj (n + 1))) :=
          Functor.congr_obj (F.comm n) (Y.obj (n + 1))
        let hY₂ :
            (F.F n).obj ((T.drop n).obj (Y.obj (n + 1))) = (F.F n).obj (Y.obj n) :=
          congrArg (fun Z => (F.F n).obj Z) (Y.compat n)
        have hMapDrop :
            (U.drop n).map ((F.F (n + 1)).map (f.app (n + 1))) =
              eqToHom hX₁ ≫ (F.F n).map ((T.drop n).map (f.app (n + 1))) ≫ eqToHom hY₁.symm := by
          simpa [Functor.comp_map] using (Functor.congr_hom (F.comm n) (f.app (n + 1)))
        have hCompat :
            (T.drop n).map (f.app (n + 1)) =
              eqToHom (X.compat n) ≫ f.app n ≫ eqToHom (Y.compat n).symm := by
          calc
            (T.drop n).map (f.app (n + 1)) =
                eqToHom (X.compat n) ≫
                  (eqToHom (X.compat n).symm ≫ (T.drop n).map (f.app (n + 1)) ≫
                    eqToHom (Y.compat n)) ≫
                  eqToHom (Y.compat n).symm := by
                simp [Category.assoc]
            _ = eqToHom (X.compat n) ≫ f.app n ≫ eqToHom (Y.compat n).symm := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t =>
                      eqToHom (X.compat n) ≫ t ≫ eqToHom (Y.compat n).symm) (f.comm n)
        have hMapCompat :
            (F.F n).map ((T.drop n).map (f.app (n + 1))) =
              eqToHom hX₂ ≫ (F.F n).map (f.app n) ≫ eqToHom hY₂.symm := by
          calc
            (F.F n).map ((T.drop n).map (f.app (n + 1))) =
                (F.F n).map (eqToHom (X.compat n) ≫ f.app n ≫ eqToHom (Y.compat n).symm) := by
                rw [hCompat]
            _ = eqToHom hX₂ ≫ (F.F n).map (f.app n) ≫ eqToHom hY₂.symm := by
                simp [Functor.map_comp]
        change
          eqToHom (hX₁.trans hX₂).symm ≫
              (U.drop n).map ((F.F (n + 1)).map (f.app (n + 1))) ≫
                eqToHom (hY₁.trans hY₂) =
            (F.F n).map (f.app n)
        calc
          eqToHom (hX₁.trans hX₂).symm ≫
              (U.drop n).map ((F.F (n + 1)).map (f.app (n + 1))) ≫
                eqToHom (hY₁.trans hY₂)
              =
            eqToHom hX₂.symm ≫
              (eqToHom hX₁.symm ≫ (U.drop n).map ((F.F (n + 1)).map (f.app (n + 1))) ≫
                eqToHom hY₁) ≫
                eqToHom hY₂ := by
              simp [Category.assoc, eqToHom_trans]
          _ = eqToHom hX₂.symm ≫ (F.F n).map ((T.drop n).map (f.app (n + 1))) ≫ eqToHom hY₂ := by
              simp [hMapDrop, Category.assoc]
          _ = (F.F n).map (f.app n) := by
              simp [hMapCompat, Category.assoc] }
  map_id := by
    intro X
    apply TowerLimit.Hom.ext
    intro n
    change (F.F n).map (𝟙 (X.obj n)) = 𝟙 ((F.F n).obj (X.obj n))
    simp
  map_comp := by
    intro X Y Z f g
    apply TowerLimit.Hom.ext
    intro n
    change (F.F n).map (f.app n ≫ g.app n) = (F.F n).map (f.app n) ≫ (F.F n).map (g.app n)
    simp

@[simp] theorem mapObj_obj (F : TowerFunctor T U) (X : TowerLimit T) (n : Nat) :
    (F.mapObj X).obj n = (F.F n).obj (X.obj n) := rfl

@[simp] theorem mapLimit_obj_obj (F : TowerFunctor T U) (X : TowerLimit T) (n : Nat) :
    (F.mapLimit.obj X).obj n = (F.F n).obj (X.obj n) := rfl

@[simp] theorem mapLimit_map_app (F : TowerFunctor T U) {X Y : TowerLimit T}
    (f : X ⟶ Y) (n : Nat) :
    ((F.mapLimit.map f).app n) = (F.F n).map (f.app n) := rfl

/-- Mapping the identity tower functor to the limit category is definitionally the identity. -/
@[simp] theorem mapLimit_id (T : CatTower.{u, v}) :
    (id T).mapLimit = 𝟭 (TowerLimit T) := by
  rfl

/-- Mapping a composite tower functor to the limit category is definitionally composition. -/
@[simp] theorem mapLimit_comp (G : TowerFunctor U V) (F : TowerFunctor T U) :
    (comp G F).mapLimit = F.mapLimit ⋙ G.mapLimit := by
  rfl

end TowerFunctor

/-- A strict tower-level natural isomorphism. Components commute strictly with the drop functors. -/
structure TowerNatIso {T U : CatTower.{u, v}} (F G : TowerFunctor T U) where
  app : ∀ n, F.F n ≅ G.F n
  hom_comm : ∀ n,
    Functor.whiskerRight (app (n + 1)).hom (U.drop n) =
      eqToHom (F.comm n) ≫ Functor.whiskerLeft (T.drop n) (app n).hom ≫ eqToHom (G.comm n).symm
  inv_comm : ∀ n,
    Functor.whiskerRight (app (n + 1)).inv (U.drop n) =
      eqToHom (G.comm n) ≫ Functor.whiskerLeft (T.drop n) (app n).inv ≫ eqToHom (F.comm n).symm

namespace TowerNatIso

variable {T U : CatTower.{u, v}} {F G H : TowerFunctor T U}

/-- Identity tower-level natural isomorphism. -/
def refl (F : TowerFunctor T U) : TowerNatIso F F where
  app := fun n => Iso.refl _
  hom_comm := by
    intro n
    simp
  inv_comm := by
    intro n
    simp

/-- Componentwise inverse tower-level natural isomorphism. -/
def symm (α : TowerNatIso F G) : TowerNatIso G F where
  app := fun n => (α.app n).symm
  hom_comm := by
    intro n
    simpa using α.inv_comm n
  inv_comm := by
    intro n
    simpa using α.hom_comm n

/-- The induced natural transformation on inverse-limit functors. -/
def mapLimitHom (α : TowerNatIso F G) : F.mapLimit ⟶ G.mapLimit where
  app := by
    intro X
    refine { app := fun n => (α.app n).hom.app (X.obj n), comm := ?_ }
    intro n
    let hF₁ :
        (U.drop n).obj ((F.F (n + 1)).obj (X.obj (n + 1))) =
          (F.F n).obj ((T.drop n).obj (X.obj (n + 1))) :=
      Functor.congr_obj (F.comm n) (X.obj (n + 1))
    let hF₂ :
        (F.F n).obj ((T.drop n).obj (X.obj (n + 1))) = (F.F n).obj (X.obj n) :=
      congrArg (fun Z => (F.F n).obj Z) (X.compat n)
    let hG₁ :
        (U.drop n).obj ((G.F (n + 1)).obj (X.obj (n + 1))) =
          (G.F n).obj ((T.drop n).obj (X.obj (n + 1))) :=
      Functor.congr_obj (G.comm n) (X.obj (n + 1))
    let hG₂ :
        (G.F n).obj ((T.drop n).obj (X.obj (n + 1))) = (G.F n).obj (X.obj n) :=
      congrArg (fun Z => (G.F n).obj Z) (X.compat n)
    have hDrop :
        (U.drop n).map ((α.app (n + 1)).hom.app (X.obj (n + 1))) =
          eqToHom hF₁ ≫ (α.app n).hom.app ((T.drop n).obj (X.obj (n + 1))) ≫ eqToHom hG₁.symm := by
      simpa using congrArg (fun τ => τ.app (X.obj (n + 1))) (α.hom_comm n)
    have hNat :
        (α.app n).hom.app ((T.drop n).obj (X.obj (n + 1))) ≫
            (G.F n).map (eqToHom (X.compat n)) =
          (F.F n).map (eqToHom (X.compat n)) ≫ (α.app n).hom.app (X.obj n) := by
      simpa using
        (NatTrans.naturality ((α.app n).hom) (eqToHom (X.compat n))).symm
    have hFCompat :
        (F.F n).map (eqToHom (X.compat n)) = eqToHom hF₂ := by
      simp
    have hGCompat :
        (G.F n).map (eqToHom (X.compat n).symm) = eqToHom hG₂.symm := by
      simp
    have hNat' :
        (α.app n).hom.app ((T.drop n).obj (X.obj (n + 1))) ≫ eqToHom hG₂ =
          eqToHom hF₂ ≫ (α.app n).hom.app (X.obj n) := by
      simpa [hFCompat, hGCompat] using hNat
    have hLast :
        eqToHom hF₂.symm ≫ (α.app n).hom.app ((T.drop n).obj (X.obj (n + 1))) ≫ eqToHom hG₂ =
          (α.app n).hom.app (X.obj n) := by
      rw [hNat']
      simp
    change
      eqToHom (hF₁.trans hF₂).symm ≫
          (U.drop n).map ((α.app (n + 1)).hom.app (X.obj (n + 1))) ≫
            eqToHom (hG₁.trans hG₂) =
        (α.app n).hom.app (X.obj n)
    calc
      eqToHom (hF₁.trans hF₂).symm ≫
          (U.drop n).map ((α.app (n + 1)).hom.app (X.obj (n + 1))) ≫
            eqToHom (hG₁.trans hG₂)
          =
        eqToHom hF₂.symm ≫
          (eqToHom hF₁.symm ≫ (U.drop n).map ((α.app (n + 1)).hom.app (X.obj (n + 1))) ≫
            eqToHom hG₁) ≫ eqToHom hG₂ := by
          simp [Category.assoc, eqToHom_trans]
      _ =
        eqToHom hF₂.symm ≫ (α.app n).hom.app ((T.drop n).obj (X.obj (n + 1))) ≫ eqToHom hG₂ := by
          simp [hDrop, Category.assoc]
      _ = (α.app n).hom.app (X.obj n) := by
          simpa using hLast
  naturality := by
    intro X Y f
    apply TowerLimit.Hom.ext
    intro n
    exact NatTrans.naturality ((α.app n).hom) (f.app n)

/-- The induced inverse natural transformation on inverse-limit functors. -/
def mapLimitInv (α : TowerNatIso F G) : G.mapLimit ⟶ F.mapLimit where
  app := by
    intro X
    refine { app := fun n => (α.app n).inv.app (X.obj n), comm := ?_ }
    intro n
    let hG₁ :
        (U.drop n).obj ((G.F (n + 1)).obj (X.obj (n + 1))) =
          (G.F n).obj ((T.drop n).obj (X.obj (n + 1))) :=
      Functor.congr_obj (G.comm n) (X.obj (n + 1))
    let hG₂ :
        (G.F n).obj ((T.drop n).obj (X.obj (n + 1))) = (G.F n).obj (X.obj n) :=
      congrArg (fun Z => (G.F n).obj Z) (X.compat n)
    let hF₁ :
        (U.drop n).obj ((F.F (n + 1)).obj (X.obj (n + 1))) =
          (F.F n).obj ((T.drop n).obj (X.obj (n + 1))) :=
      Functor.congr_obj (F.comm n) (X.obj (n + 1))
    let hF₂ :
        (F.F n).obj ((T.drop n).obj (X.obj (n + 1))) = (F.F n).obj (X.obj n) :=
      congrArg (fun Z => (F.F n).obj Z) (X.compat n)
    have hDrop :
        (U.drop n).map ((α.app (n + 1)).inv.app (X.obj (n + 1))) =
          eqToHom hG₁ ≫ (α.app n).inv.app ((T.drop n).obj (X.obj (n + 1))) ≫ eqToHom hF₁.symm := by
      simpa using congrArg (fun τ => τ.app (X.obj (n + 1))) (α.inv_comm n)
    have hNat :
        (α.app n).inv.app ((T.drop n).obj (X.obj (n + 1))) ≫
            (F.F n).map (eqToHom (X.compat n)) =
          (G.F n).map (eqToHom (X.compat n)) ≫ (α.app n).inv.app (X.obj n) := by
      simpa using
        (NatTrans.naturality ((α.app n).inv) (eqToHom (X.compat n))).symm
    have hGCompat :
        (G.F n).map (eqToHom (X.compat n)) = eqToHom hG₂ := by
      simp
    have hFCompat :
        (F.F n).map (eqToHom (X.compat n).symm) = eqToHom hF₂.symm := by
      simp
    have hNat' :
        (α.app n).inv.app ((T.drop n).obj (X.obj (n + 1))) ≫ eqToHom hF₂ =
          eqToHom hG₂ ≫ (α.app n).inv.app (X.obj n) := by
      simpa [hGCompat, hFCompat] using hNat
    have hLast :
        eqToHom hG₂.symm ≫ (α.app n).inv.app ((T.drop n).obj (X.obj (n + 1))) ≫ eqToHom hF₂ =
          (α.app n).inv.app (X.obj n) := by
      rw [hNat']
      simp
    change
      eqToHom (hG₁.trans hG₂).symm ≫
          (U.drop n).map ((α.app (n + 1)).inv.app (X.obj (n + 1))) ≫
            eqToHom (hF₁.trans hF₂) =
        (α.app n).inv.app (X.obj n)
    calc
      eqToHom (hG₁.trans hG₂).symm ≫
          (U.drop n).map ((α.app (n + 1)).inv.app (X.obj (n + 1))) ≫
            eqToHom (hF₁.trans hF₂)
          =
        eqToHom hG₂.symm ≫
          (eqToHom hG₁.symm ≫ (U.drop n).map ((α.app (n + 1)).inv.app (X.obj (n + 1))) ≫
            eqToHom hF₁) ≫ eqToHom hF₂ := by
          simp [Category.assoc, eqToHom_trans]
      _ =
        eqToHom hG₂.symm ≫ (α.app n).inv.app ((T.drop n).obj (X.obj (n + 1))) ≫ eqToHom hF₂ := by
          simp [hDrop, Category.assoc]
      _ = (α.app n).inv.app (X.obj n) := by
          simpa using hLast
  naturality := by
    intro X Y f
    apply TowerLimit.Hom.ext
    intro n
    exact NatTrans.naturality ((α.app n).inv) (f.app n)

/-- A strict tower-level natural isomorphism induces one on inverse-limit categories. -/
def mapLimitIso (α : TowerNatIso F G) : F.mapLimit ≅ G.mapLimit where
  hom := α.mapLimitHom
  inv := α.mapLimitInv
  hom_inv_id := by
    ext X
    apply TowerLimit.Hom.ext
    intro n
    simp [mapLimitHom, mapLimitInv]
  inv_hom_id := by
    ext X
    apply TowerLimit.Hom.ext
    intro n
    simp [mapLimitHom, mapLimitInv]

end TowerNatIso

/-- Strict equivalence data between two category towers. -/
structure TowerEquivalence (T U : CatTower.{u, v}) where
  F : TowerFunctor T U
  G : TowerFunctor U T
  unitIso : TowerNatIso (TowerFunctor.id T) (TowerFunctor.comp G F)
  counitIso : TowerNatIso (TowerFunctor.comp F G) (TowerFunctor.id U)
  functor_unitIso_comp :
    ∀ n (X : T.Obj n),
      (F.F n).map ((unitIso.app n).hom.app X) ≫
        (counitIso.app n).hom.app ((F.F n).obj X) =
      𝟙 ((F.F n).obj X)

namespace TowerEquivalence

variable {T U : CatTower.{u, v}}

/-- Strict tower equivalence induces an equivalence on inverse-limit categories. -/
noncomputable def mapLimitEquivalence (e : TowerEquivalence T U) :
    TowerLimit T ≌ TowerLimit U where
  functor := e.F.mapLimit
  inverse := e.G.mapLimit
  unitIso :=
    (eqToIso (TowerFunctor.mapLimit_id T)).symm ≪≫
      e.unitIso.mapLimitIso ≪≫
      eqToIso (TowerFunctor.mapLimit_comp e.G e.F)
  counitIso :=
    (eqToIso (TowerFunctor.mapLimit_comp e.F e.G)).symm ≪≫
      e.counitIso.mapLimitIso ≪≫
      eqToIso (TowerFunctor.mapLimit_id U)
  functor_unitIso_comp := by
    intro X
    apply TowerLimit.Hom.ext
    intro n
    simpa [TowerFunctor.id, TowerFunctor.comp,
      TowerFunctor.mapLimit_id, TowerFunctor.mapLimit_comp,
      TowerNatIso.mapLimitIso, TowerNatIso.mapLimitHom, Category.assoc] using
      e.functor_unitIso_comp n (X.obj n)

end TowerEquivalence

/-- Public theorem form of the strict tower-limit equivalence principle. -/
noncomputable def towerLimit_equivalence_of_towerEquivalence {T U : CatTower.{u, v}}
    (e : TowerEquivalence T U) : TowerLimit T ≌ TowerLimit U :=
  e.mapLimitEquivalence

end HomotopyTower
end Algebra
end HeytingLean
