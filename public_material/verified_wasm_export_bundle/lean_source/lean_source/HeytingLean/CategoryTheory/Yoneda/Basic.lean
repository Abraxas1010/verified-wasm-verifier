import Mathlib.CategoryTheory.Yoneda
import HeytingLean.ClosingTheLoop.Cat.Concreteness

namespace HeytingLean
namespace CategoryTheory
namespace Yoneda

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Yoneda is faithful: equality of Yoneda-mapped morphisms reflects. -/
theorem yoneda_map_injective {X Y : C} {f g : X ⟶ Y}
    (h : _root_.CategoryTheory.yoneda.map f = _root_.CategoryTheory.yoneda.map g) :
    f = g := by
  exact (Functor.map_injective (_root_.CategoryTheory.yoneda : C ⥤ (Cᵒᵖ ⥤ Type v))) h

/-- Idempotence can be reflected from the Yoneda embedding. -/
theorem yoneda_reflects_idempotence {X : C} (f : X ⟶ X)
    (h :
      (_root_.CategoryTheory.yoneda.map f) ≫ (_root_.CategoryTheory.yoneda.map f) =
        _root_.CategoryTheory.yoneda.map f) :
    f ≫ f = f :=
  ClosingTheLoop.Cat.idem_of_yoneda_map_idem (C := C) f h

end Yoneda
end CategoryTheory
end HeytingLean
