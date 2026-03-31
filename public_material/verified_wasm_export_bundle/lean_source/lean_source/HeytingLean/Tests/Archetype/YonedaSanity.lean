import HeytingLean.CategoryTheory.Yoneda.README

open _root_.CategoryTheory

example {C : Type} [Category C] {X Y : C} {f g : X ⟶ Y}
    (h : _root_.CategoryTheory.yoneda.map f = _root_.CategoryTheory.yoneda.map g) :
    f = g := by
  exact HeytingLean.CategoryTheory.Yoneda.yoneda_map_injective (C := C) h

example {L : Type} [SemilatticeInf L] [OrderBot L]
    (N : HeytingLean.Core.Nucleus L) (x : L) :
    x ≤ N.R x := by
  exact HeytingLean.CategoryTheory.Yoneda.nucleus_fixedpoints_are_stable_under_reflection N x
