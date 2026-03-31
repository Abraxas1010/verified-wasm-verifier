import Mathlib.CategoryTheory.Category.Basic
import HeytingLean.IteratedVirtual.NGlobular
import HeytingLean.IteratedVirtual.GlobeN

/-!
# IteratedVirtual.StrictN

A minimal **strict n-category** notion:

- an underlying truncated globular set `NGlobularSet n`,
- for each `k < n`, a category structure on `k`-cells with morphisms `(k+1)`-cells.

This avoids requiring any data about `(n+1)`-cells to speak about `n`-cells.
-/

namespace HeytingLean
namespace IteratedVirtual

universe u

open CategoryTheory

open NGlobularSet

structure StrictNCategory (n : Nat) where
  G : NGlobularSet n

  idCell :
      ∀ k : Nat, ∀ hk : k < n, ∀ a : G.Cell k,
        { f : G.Cell (k + 1) // G.src k hk f = a ∧ G.tgt k hk f = a }

  compCell :
      ∀ k : Nat, ∀ hk : k < n, ∀ {a b c : G.Cell k},
        { f : G.Cell (k + 1) // G.src k hk f = a ∧ G.tgt k hk f = b } →
          { g : G.Cell (k + 1) // G.src k hk g = b ∧ G.tgt k hk g = c } →
            { h : G.Cell (k + 1) // G.src k hk h = a ∧ G.tgt k hk h = c }

  id_comp :
      ∀ k : Nat, ∀ hk : k < n, ∀ {a b : G.Cell k}
        (f : { f : G.Cell (k + 1) // G.src k hk f = a ∧ G.tgt k hk f = b }),
          compCell k hk (idCell k hk a) f = f

  comp_id :
      ∀ k : Nat, ∀ hk : k < n, ∀ {a b : G.Cell k}
        (f : { f : G.Cell (k + 1) // G.src k hk f = a ∧ G.tgt k hk f = b }),
          compCell k hk f (idCell k hk b) = f

  assoc :
      ∀ k : Nat, ∀ hk : k < n, ∀ {a b c d : G.Cell k}
        (f : { f : G.Cell (k + 1) // G.src k hk f = a ∧ G.tgt k hk f = b })
        (g : { g : G.Cell (k + 1) // G.src k hk g = b ∧ G.tgt k hk g = c })
        (h : { h : G.Cell (k + 1) // G.src k hk h = c ∧ G.tgt k hk h = d }),
          compCell k hk (compCell k hk f g) h = compCell k hk f (compCell k hk g h)

namespace StrictNCategory

abbrev HomAt (C : StrictNCategory n) (k : Nat) (hk : k < n) (a b : C.G.Cell k) :=
  { f : C.G.Cell (k + 1) // C.G.src k hk f = a ∧ C.G.tgt k hk f = b }

instance categoryAt (C : StrictNCategory n) (k : Nat) (hk : k < n) : Category (C.G.Cell k) where
  Hom a b := HomAt (n := n) C k hk a b
  id a := C.idCell k hk a
  comp f g := C.compCell k hk f g
  id_comp := by intro a b f; simpa using C.id_comp k hk (a := a) (b := b) f
  comp_id := by intro a b f; simpa using C.comp_id k hk (a := a) (b := b) f
  assoc := by
    intro a b c d f g h
    simpa using C.assoc k hk (a := a) (b := b) (c := c) (d := d) f g h

/-- A “top n-cell” presented as a map from the walking `n`-globe into the underlying globular data. -/
abbrev CellTop (C : StrictNCategory n) :=
  NGlobularSet.Hom (X := GlobeN n) (Y := C.G)

/-- A “k-cell in an n-category” for `k ≤ n`, as a globe-map into the `k`-truncation of the underlying globular data. -/
abbrev kCell (C : StrictNCategory n) (k : Nat) (hk : k ≤ n) :=
  NGlobularSet.Hom (X := GlobeN k) (Y := (C.G.restrict k hk))

end StrictNCategory

end IteratedVirtual
end HeytingLean
