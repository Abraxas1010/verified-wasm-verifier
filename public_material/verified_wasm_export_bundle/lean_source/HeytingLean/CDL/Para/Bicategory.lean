import Mathlib.CategoryTheory.Bicategory.Basic
import HeytingLean.CDL.Para.Type

/-!
# CDL: `Para(Type)` as a Mathlib bicategory

We keep `HeytingLean.CDL.Para.ParaHom`/`Para2Hom` as the computational core, and provide a
Mathlib `Bicategory` instance on a **wrapper** type of objects. The wrapper avoids conflicting
with the standard `Category (Type u)` instance (whose 1-morphisms are functions).

This gives a principled home for:
- whiskering (`◁`, `▷`) as horizontal composition of reparameterizations,
- associator / unitors as the explicit coherence isomorphisms already defined for `ParaHom`.
-/

namespace HeytingLean
namespace CDL
namespace Para

universe u

/-- Objects of the bicategory `Para(Type u)` (wrapper to avoid instance conflicts). -/
structure Obj : Type (u + 1) where
  carrier : Type u

instance : CoeSort Obj (Sort (u + 1)) :=
  ⟨Obj.carrier⟩

namespace Obj

@[simp] theorem eta (X : Obj) : Obj.mk X.carrier = X := by
  cases X
  rfl

end Obj

open CategoryTheory

@[nolint checkUnivs]
instance : Bicategory Obj where
  Hom X Y := ParaHom X Y
  id X := ParaHom.id X
  comp f g := ParaHom.comp g f
  homCategory X Y := inferInstance
  whiskerLeft := by
    intro a b c f g h η
    exact Para2Hom.hcomp (α := Para2Hom.refl f) (β := η)
  whiskerRight := by
    intro a b c f g η h
    exact Para2Hom.hcomp (α := η) (β := Para2Hom.refl h)
  associator := fun f g h => Coherence.assoc h g f
  leftUnitor := fun f => Coherence.rightUnitor f
  rightUnitor := fun f => Coherence.leftUnitor f
  whiskerLeft_id := by
    intro a b c f g
    apply Para2Hom.ext
    rfl
  whiskerLeft_comp := by
    intro a b c f g h i η θ
    apply Para2Hom.ext
    rfl
  id_whiskerLeft := by
    intro a b f g η
    apply Para2Hom.ext
    rfl
  comp_whiskerLeft := by
    intro a b c d f g h h' η
    apply Para2Hom.ext
    rfl
  id_whiskerRight := by
    intro a b c f g
    apply Para2Hom.ext
    rfl
  comp_whiskerRight := by
    intro a b c f g h η θ i
    apply Para2Hom.ext
    rfl
  whiskerRight_id := by
    intro a b f g η
    apply Para2Hom.ext
    rfl
  whiskerRight_comp := by
    intro a b c d f f' η g h
    apply Para2Hom.ext
    rfl
  whisker_assoc := by
    intro a b c d f g g' η h
    apply Para2Hom.ext
    rfl
  whisker_exchange := by
    intro a b c f g h i η θ
    apply Para2Hom.ext
    rfl
  pentagon := by
    intro a b c d e f g h i
    apply Para2Hom.ext
    rfl
  triangle := by
    intro a b c f g
    apply Para2Hom.ext
    rfl

end Para
end CDL
end HeytingLean
