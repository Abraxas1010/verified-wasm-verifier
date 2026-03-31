import HeytingLean.HigherCategory.Opetope.Basic
import HeytingLean.CategoryTheory.Polynomial.Basic

namespace HeytingLean
namespace HigherCategory
namespace Opetope

open _root_.CategoryTheory.Polynomial

universe u

/-- The degree-`n` cell type of a globular opetope interpreted as a polynomial shape family. -/
abbrev cellPoly (X : GlobularOpetope.{u}) (n : Nat) : Poly :=
  (IteratedVirtual.GlobularSetPsh.Cell X n) y^PUnit

def srcPolymap (X : GlobularOpetope.{u}) (n : Nat) :
    polymap (cellPoly X (n + 1)) (cellPoly X n) where
  onPos := IteratedVirtual.GlobularSetPsh.src (X := X) (n := n)
  onDir := fun _ _ => PUnit.unit

def tgtPolymap (X : GlobularOpetope.{u}) (n : Nat) :
    polymap (cellPoly X (n + 1)) (cellPoly X n) where
  onPos := IteratedVirtual.GlobularSetPsh.tgt (X := X) (n := n)
  onDir := fun _ _ => PUnit.unit

theorem src_src_eq_src_tgt_via_polymaps
    (X : GlobularOpetope.{u}) (n : Nat)
    (x : IteratedVirtual.GlobularSetPsh.Cell X (n + 2)) :
    (composemap (srcPolymap X (n + 1)) (srcPolymap X n)).onPos x =
      (composemap (tgtPolymap X (n + 1)) (srcPolymap X n)).onPos x := by
  simpa [srcPolymap, tgtPolymap, composemap] using source_target_globular_law X n x

theorem tgt_src_eq_tgt_tgt_via_polymaps
    (X : GlobularOpetope.{u}) (n : Nat)
    (x : IteratedVirtual.GlobularSetPsh.Cell X (n + 2)) :
    (composemap (srcPolymap X (n + 1)) (tgtPolymap X n)).onPos x =
      (composemap (tgtPolymap X (n + 1)) (tgtPolymap X n)).onPos x := by
  simpa [srcPolymap, tgtPolymap, composemap] using target_target_globular_law X n x

end Opetope
end HigherCategory
end HeytingLean
