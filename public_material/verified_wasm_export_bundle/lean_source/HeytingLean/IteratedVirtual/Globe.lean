import HeytingLean.IteratedVirtual.Globular

/-!
# IteratedVirtual.Globe

Walking globes as *globular sets*.

We use a simple explicit model:
- for dimensions `< k`, there are two boundary cells (`Fin 2`);
- for dimensions `≥ k`, there is a single cell (`PUnit`).

This is sufficient to define “a k-cell in X” as a globular map `Globe k ⟶ X`.
-/

namespace HeytingLean
namespace IteratedVirtual

open GlobularSet

universe u

namespace Globe

/-- The underlying level type of the walking `k`-globe at dimension `n`. -/
def Cell (k n : Nat) : Type u :=
  ULift.{0, u} (Sum (PLift (n < k) × Fin 2) (PLift (¬n < k) × PUnit))

def boundary {k n : Nat} (hn : n < k) (b : Fin 2) : Cell k n :=
  ULift.up (Sum.inl ⟨⟨hn⟩, b⟩)

def top {k : Nat} : Cell k k :=
  ULift.up (Sum.inr ⟨⟨by simp⟩, PUnit.unit⟩)

private def src {k n : Nat} : Cell k (n + 1) → Cell k n := by
  intro _
  by_cases hn : n < k
  · exact ULift.up (Sum.inl ⟨⟨hn⟩, (⟨0, by decide⟩ : Fin 2)⟩)
  · exact ULift.up (Sum.inr ⟨⟨hn⟩, PUnit.unit⟩)

private def tgt {k n : Nat} : Cell k (n + 1) → Cell k n := by
  intro _
  by_cases hn : n < k
  · exact ULift.up (Sum.inl ⟨⟨hn⟩, (⟨1, by decide⟩ : Fin 2)⟩)
  · exact ULift.up (Sum.inr ⟨⟨hn⟩, PUnit.unit⟩)

private theorem src_src_eq_src_tgt {k n : Nat} (x : Cell k (n + 2)) :
    src (k := k) (n := n) (src (k := k) (n := n + 1) x) =
      src (k := k) (n := n) (tgt (k := k) (n := n + 1) x) := by
  by_cases hn : n < k <;> simp [src, Cell, hn]

private theorem tgt_src_eq_tgt_tgt {k n : Nat} (x : Cell k (n + 2)) :
    tgt (k := k) (n := n) (src (k := k) (n := n + 1) x) =
      tgt (k := k) (n := n) (tgt (k := k) (n := n + 1) x) := by
  by_cases hn : n < k <;> simp [tgt, Cell, hn]

end Globe

/-- The walking `k`-globe as a globular set. -/
def Globe (k : Nat) : GlobularSet.{u} where
  Cell := Globe.Cell k
  src := Globe.src
  tgt := Globe.tgt
  src_src_eq_src_tgt := Globe.src_src_eq_src_tgt
  tgt_src_eq_tgt_tgt := Globe.tgt_src_eq_tgt_tgt

/-- A `k`-cell of a globular set `X` is a globular-set morphism `Globe k ⟶ X`. -/
abbrev kCell (X : GlobularSet.{u}) (k : Nat) :=
  GlobularSet.Hom.{u} (Globe k) X

namespace kCell

def srcCell {X : GlobularSet.{u}} {k : Nat} (A : IteratedVirtual.kCell (X := X) k) (n : Nat) (hn : n < k) :
    X.Cell n :=
  A.map n (Globe.boundary (k := k) (n := n) hn (⟨0, by decide⟩ : Fin 2))

def tgtCell {X : GlobularSet.{u}} {k : Nat} (A : IteratedVirtual.kCell (X := X) k) (n : Nat) (hn : n < k) :
    X.Cell n :=
  A.map n (Globe.boundary (k := k) (n := n) hn (⟨1, by decide⟩ : Fin 2))

end kCell

end IteratedVirtual
end HeytingLean
