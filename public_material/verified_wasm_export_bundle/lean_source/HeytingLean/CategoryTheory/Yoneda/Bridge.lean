import HeytingLean.CategoryTheory.Yoneda.Basic
import HeytingLean.Core.Nucleus

namespace HeytingLean
namespace CategoryTheory
namespace Yoneda

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]
variable {L : Type*} [SemilatticeInf L] [OrderBot L]

theorem yoneda_idempotence_bridge {X : C} (f : X ⟶ X)
    (h :
      (_root_.CategoryTheory.yoneda.map f) ≫ (_root_.CategoryTheory.yoneda.map f) =
        _root_.CategoryTheory.yoneda.map f) :
    f ≫ f = f :=
  yoneda_reflects_idempotence (C := C) f h

theorem nucleus_fixedpoints_are_stable_under_reflection (N : Core.Nucleus L) (x : L) :
    x ≤ N.R x := by
  exact N.extensive x

end Yoneda
end CategoryTheory
end HeytingLean
