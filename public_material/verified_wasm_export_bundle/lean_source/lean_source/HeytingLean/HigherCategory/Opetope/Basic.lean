import HeytingLean.IteratedVirtual.GlobularPresheaf

namespace HeytingLean
namespace HigherCategory
namespace Opetope

open _root_.CategoryTheory

universe u

/-- Opetopic context modelled by globular presheaves. -/
abbrev GlobularOpetope : Type (u + 1) :=
  IteratedVirtual.GlobularSetPsh.{u}

abbrev globe (n : Nat) : GlobularOpetope.{u} :=
  IteratedVirtual.GlobePsh.{u} n

abbrev kCell (X : GlobularOpetope.{u}) (k : Nat) :=
  IteratedVirtual.kCellPsh (X := X) k

theorem source_target_globular_law
    (X : GlobularOpetope.{u}) (n : Nat)
    (x : IteratedVirtual.GlobularSetPsh.Cell X (n + 2)) :
    IteratedVirtual.GlobularSetPsh.src (n := n)
        (IteratedVirtual.GlobularSetPsh.src (n := n + 1) x) =
      IteratedVirtual.GlobularSetPsh.src (n := n)
        (IteratedVirtual.GlobularSetPsh.tgt (n := n + 1) x) :=
  IteratedVirtual.GlobularSetPsh.src_src_eq_src_tgt x

theorem target_target_globular_law
    (X : GlobularOpetope.{u}) (n : Nat)
    (x : IteratedVirtual.GlobularSetPsh.Cell X (n + 2)) :
    IteratedVirtual.GlobularSetPsh.tgt (n := n)
        (IteratedVirtual.GlobularSetPsh.src (n := n + 1) x) =
      IteratedVirtual.GlobularSetPsh.tgt (n := n)
        (IteratedVirtual.GlobularSetPsh.tgt (n := n + 1) x) :=
  IteratedVirtual.GlobularSetPsh.tgt_src_eq_tgt_tgt x

end Opetope
end HigherCategory
end HeytingLean
