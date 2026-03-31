import HeytingLean.Topos.LocSys.LocalSystems

namespace HeytingLean
namespace Topos
namespace LocSys

open CategoryTheory

universe uK uB vB

variable (K : Type uK) [CommRing K]

/--
`Loc K` is a “Grothendieck-style” total category of `K`-linear local systems over varying
1-type bases (groupoids).

Objects are pairs `(X, V)` with `X : Grpd` and `V : X ⥤ Coeff K`.
Morphisms `(X,V) ⟶ (Y,W)` are pairs `(f : X ⥤ Y, φ : V ⟶ f*W)` where `f*` is pullback by
precomposition.
-/
structure Loc where
  /-- The base groupoid. -/
  base : Grpd.{vB, uB}
  /-- A local system over `base`. -/
  sys : LocalSystem K base

namespace Loc

variable {K}

/-- A morphism in `Loc K` is a base functor plus a fiber map into the pulled-back system. -/
structure Hom (X Y : Loc (K := K)) where
  /-- The base functor. -/
  base : X.base ⟶ Y.base
  /-- The map on local systems: `X.sys ⟶ base* Y.sys`. -/
  fiber : X.sys ⟶ (LocalSystems.pullback (K := K) base).obj Y.sys

@[simp] theorem Hom.base_mk {X Y : Loc (K := K)} (f : X.base ⟶ Y.base)
    (φ : X.sys ⟶ (LocalSystems.pullback (K := K) f).obj Y.sys) :
    (Hom.mk f φ).base = f := rfl

@[simp] theorem Hom.fiber_mk {X Y : Loc (K := K)} (f : X.base ⟶ Y.base)
    (φ : X.sys ⟶ (LocalSystems.pullback (K := K) f).obj Y.sys) :
    (Hom.mk f φ).fiber = φ := rfl

/-- Identity morphism in `Loc K`. -/
def id (X : Loc (K := K)) : Hom X X where
  base := 𝟙 X.base
  fiber := 𝟙 X.sys

/-- Composition of morphisms in `Loc K`. -/
def comp {X Y Z : Loc (K := K)} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber := f.fiber ≫ (LocalSystems.pullback (K := K) f.base).map g.fiber

instance : Category (Loc (K := K)) where
  Hom X Y := Hom X Y
  id X := id (K := K) X
  comp f g := comp (K := K) f g
  id_comp f := by
    cases f
    rfl
  comp_id f := by
    cases f
    rfl
  assoc f g h := by
    cases f
    cases g
    cases h
    -- `Functor.associator` for functor composition is definitional (`Iso.refl`), but not a simp lemma.
    -- After expanding, `rfl` closes the remaining coherence goal.
    rfl

@[simp] theorem id_base (X : Loc (K := K)) : (𝟙 X : X ⟶ X).base = 𝟙 X.base := rfl
@[simp] theorem id_fiber (X : Loc (K := K)) : (𝟙 X : X ⟶ X).fiber = 𝟙 X.sys := rfl

@[simp] theorem comp_base {X Y Z : Loc (K := K)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

@[simp] theorem comp_fiber {X Y Z : Loc (K := K)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber = f.fiber ≫ (LocalSystems.pullback (K := K) f.base).map g.fiber := rfl

/-- Projection `Loc K ⥤ Grpd` forgetting the local system. -/
def π : Loc (K := K) ⥤ Grpd.{vB, uB} where
  obj X := X.base
  map f := f.base

@[simp] theorem π_obj (X : Loc (K := K)) : (π (K := K)).obj X = X.base := rfl
@[simp] theorem π_map {X Y : Loc (K := K)} (f : X ⟶ Y) : (π (K := K)).map f = f.base := rfl

@[ext]
theorem hom_ext {X Y : Loc (K := K)} (f g : X ⟶ Y) (hbase : f.base = g.base)
    (hfiber : HEq f.fiber g.fiber) : f = g := by
  cases f
  cases g
  cases hbase
  cases hfiber
  rfl

end Loc

end LocSys
end Topos
end HeytingLean
