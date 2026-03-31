import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import HeytingLean.CDL.Para.Bicategory
import HeytingLean.CDL.StrongMonad

/-!
# CDL: `Para(T)` as a pseudofunctor on `Para(Type)`

CDL lifts a (strong) monad `T` on the base category to an endo-(pseudo)functor on the
parametric bicategory `Para(Type)` (CDL Example G.8).

In this repo’s cartesian `Type` specialization, the lift is:
- on objects: `X ↦ T X`,
- on 1-cells: `(P, f : P × X → Y) ↦ (P, fun (p, tx) => f p <$> tx)`,
- on 2-cells: reparameterizations are unchanged.

We package this as a Mathlib `Pseudofunctor` on the bicategory `HeytingLean.CDL.Para.Obj`.
-/

namespace HeytingLean
namespace CDL
namespace Para

universe u

open CategoryTheory

variable (T : Type u → Type u) [StrongMonad T] [LawfulMonad T]

namespace paraT_aux

open HeytingLean.CDL.Para

/-- Inverse of `Para.map_id` as a 2-morphism. -/
def map_id_inv (X : Type u) : Para2Hom (ParaHom.id (T X)) (Para.map (T := T) (ParaHom.id X)) := by
  refine ⟨id, ?_⟩
  intro p tx
  cases p
  have h := (Para.map_id (T := T) (X := X)).comm PUnit.unit tx
  simpa using h.symm

/-- Inverse of `Para.map_comp` as a 2-morphism. -/
def map_comp_inv {X Y Z : Type u} (g : ParaHom Y Z) (f : ParaHom X Y) :
    Para2Hom (ParaHom.comp (Para.map (T := T) g) (Para.map (T := T) f)) (Para.map (T := T) (ParaHom.comp g f)) := by
  refine ⟨id, ?_⟩
  intro p tx
  have h := (Para.map_comp (T := T) (g := g) (f := f)).comm p tx
  simpa using h.symm

end paraT_aux

@[nolint checkUnivs]
def paraT : Pseudofunctor (Obj.{u}) (Obj.{u}) where
  obj X := ⟨T X⟩
  map {X Y} f := Para.map (T := T) f
  map₂ {X Y} {f g} η := Para.map₂ (T := T) η
  mapId X :=
    { hom := Para.map_id (T := T) (X := X)
      inv := paraT_aux.map_id_inv (T := T) (X := X)
      hom_inv_id := by
        apply Para2Hom.ext
        rfl
      inv_hom_id := by
        apply Para2Hom.ext
        rfl }
  mapComp {X Y Z} f g :=
    { hom := Para.map_comp (T := T) (g := g) (f := f)
      inv := paraT_aux.map_comp_inv (T := T) (g := g) (f := f)
      hom_inv_id := by
        apply Para2Hom.ext
        rfl
      inv_hom_id := by
        apply Para2Hom.ext
        rfl }
  map₂_whisker_left := by
    intro a b c f g h η
    apply Para2Hom.ext
    rfl
  map₂_whisker_right := by
    intro a b c f g η h
    apply Para2Hom.ext
    rfl
  map₂_associator := by
    intro a b c d f g h
    apply Para2Hom.ext
    rfl
  map₂_left_unitor := by
    intro a b f
    apply Para2Hom.ext
    rfl
  map₂_right_unitor := by
    intro a b f
    apply Para2Hom.ext
    rfl

end Para
end CDL
end HeytingLean
