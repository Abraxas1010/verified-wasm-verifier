import HeytingLean.CategoryTheory.KanExtension.README

open _root_.CategoryTheory

example {L : Type} [SemilatticeInf L] [OrderBot L]
    (N : HeytingLean.Core.Nucleus L) (x : L) :
    x ≤ N.R x := by
  exact HeytingLean.CategoryTheory.KanExtension.nucleus_extensive_bridge N x

example {K : Type} [CommRing K] {X Y : Grpd} (f : X ⥤ Y)
    (V : HeytingLean.Topos.LocSys.LocalSystem (K := K) Y) :
    (HeytingLean.CategoryTheory.KanExtension.pullbackLocalSystem (K := K) f).obj V = f ⋙ V := by
  exact HeytingLean.CategoryTheory.KanExtension.pullback_obj_eq_precompose (K := K) f V
