import HeytingLean.CategoryTheory.Yoneda.Bridge

namespace HeytingLean
namespace Bridges
namespace Archetype

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

theorem yoneda_to_eigenform_idempotence {X : C} (f : X ⟶ X)
    (h :
      (_root_.CategoryTheory.yoneda.map f) ≫ (_root_.CategoryTheory.yoneda.map f) =
        _root_.CategoryTheory.yoneda.map f) :
    f ≫ f = f :=
  CategoryTheory.Yoneda.yoneda_idempotence_bridge (C := C) f h

end Archetype
end Bridges
end HeytingLean
