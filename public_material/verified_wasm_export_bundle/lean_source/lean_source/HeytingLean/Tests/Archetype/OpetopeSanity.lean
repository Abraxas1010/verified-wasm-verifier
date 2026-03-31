import HeytingLean.HigherCategory.Opetope.README

universe u

example (X : HeytingLean.HigherCategory.Opetope.GlobularOpetope.{u}) (n : Nat)
    (x : HeytingLean.IteratedVirtual.GlobularSetPsh.Cell X (n + 2)) :
    (_root_.CategoryTheory.Polynomial.composemap
      (HeytingLean.HigherCategory.Opetope.srcPolymap X (n + 1))
      (HeytingLean.HigherCategory.Opetope.srcPolymap X n)).onPos x =
    (_root_.CategoryTheory.Polynomial.composemap
      (HeytingLean.HigherCategory.Opetope.tgtPolymap X (n + 1))
      (HeytingLean.HigherCategory.Opetope.srcPolymap X n)).onPos x := by
  exact HeytingLean.HigherCategory.Opetope.src_src_eq_src_tgt_via_polymaps X n x

example (X : HeytingLean.HigherCategory.Opetope.GlobularOpetope.{u}) (n : Nat)
    (x : HeytingLean.IteratedVirtual.GlobularSetPsh.Cell X (n + 2)) :
    (_root_.CategoryTheory.Polynomial.composemap
      (HeytingLean.HigherCategory.Opetope.srcPolymap X (n + 1))
      (HeytingLean.HigherCategory.Opetope.tgtPolymap X n)).onPos x =
    (_root_.CategoryTheory.Polynomial.composemap
      (HeytingLean.HigherCategory.Opetope.tgtPolymap X (n + 1))
      (HeytingLean.HigherCategory.Opetope.tgtPolymap X n)).onPos x := by
  exact HeytingLean.HigherCategory.Opetope.tgt_src_eq_tgt_tgt_via_polymaps X n x
