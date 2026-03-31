import Mathlib.CategoryTheory.Category.Basic
import HeytingLean.IteratedVirtual.Globe

/-!
# IteratedVirtual.StrictOmega

Minimal “strict globular ω-category” layer:

- a globular set `G`,
- for each dimension `n`, a **category structure** on `n`-cells, whose morphisms are `(n+1)`-cells
  with domain/codomain given by `src`/`tgt`.

This is intentionally weaker than the full nLab definition of strict ω-categories (which also
includes multiple compositions and interchange laws). It is sufficient to:
- talk about “a k-cell as a map `Globe k ⟶ underlying(G)`”, and
- have actual coherence laws (associativity/unit) for adjacent-dimensional composition.
-/

namespace HeytingLean
namespace IteratedVirtual

universe u

open CategoryTheory

open GlobularSet

structure StrictOmegaCategory where
  G : GlobularSet.{u}

  /-- Identity (n+1)-cell on an n-cell, packaged as a morphism with matching boundaries. -/
  idCell : ∀ {n : Nat} (a : G.Cell n), { f : G.Cell (n + 1) // G.src f = a ∧ G.tgt f = a }

  /-- Composition of (n+1)-cells (as morphisms between n-cells). -/
  compCell :
      ∀ {n : Nat} {a b c : G.Cell n},
        { f : G.Cell (n + 1) // G.src f = a ∧ G.tgt f = b } →
          { g : G.Cell (n + 1) // G.src g = b ∧ G.tgt g = c } →
            { h : G.Cell (n + 1) // G.src h = a ∧ G.tgt h = c }

  id_comp :
      ∀ {n : Nat} {a b : G.Cell n}
        (f : { f : G.Cell (n + 1) // G.src f = a ∧ G.tgt f = b }),
          compCell (idCell (n := n) a) f = f

  comp_id :
      ∀ {n : Nat} {a b : G.Cell n}
        (f : { f : G.Cell (n + 1) // G.src f = a ∧ G.tgt f = b }),
          compCell f (idCell (n := n) b) = f

  assoc :
      ∀ {n : Nat} {a b c d : G.Cell n}
        (f : { f : G.Cell (n + 1) // G.src f = a ∧ G.tgt f = b })
        (g : { g : G.Cell (n + 1) // G.src g = b ∧ G.tgt g = c })
        (h : { h : G.Cell (n + 1) // G.src h = c ∧ G.tgt h = d }),
          compCell (compCell f g) h = compCell f (compCell g h)

namespace StrictOmegaCategory

abbrev Hom (C : StrictOmegaCategory.{u}) (n : Nat) (a b : C.G.Cell n) :=
  { f : C.G.Cell (n + 1) // C.G.src f = a ∧ C.G.tgt f = b }

instance categoryAt (C : StrictOmegaCategory.{u}) (n : Nat) : Category (C.G.Cell n) where
  Hom a b := Hom C n a b
  id a := C.idCell (n := n) a
  comp f g := C.compCell f g
  id_comp := by intro a b f; simpa using C.id_comp (n := n) (a := a) (b := b) f
  comp_id := by intro a b f; simpa using C.comp_id (n := n) (a := a) (b := b) f
  assoc := by
    intro a b c d f g h
    simpa using C.assoc (n := n) (a := a) (b := b) (c := c) (d := d) f g h

end StrictOmegaCategory

/-!
## A minimal “Catₙ” wrapper
-/

structure StrictNCat (n : Nat) where
  C : StrictOmegaCategory.{u}
  trunc : ∀ m : Nat, n < m → Subsingleton (C.G.Cell m)

namespace StrictNCat

/-- An “n-cell” in a strict `n`-category, presented as a globe-map into its underlying globular set. -/
abbrev nCell (n : Nat) (C : StrictNCat n) :=
  kCell (X := C.C.G) n

abbrev Cell22 (C : StrictNCat 22) :=
  nCell 22 C

end StrictNCat

/-!
## Example: the terminal strict ω-category
-/

namespace Examples

def terminalGlobularSet : GlobularSet where
  Cell := fun _ => PUnit
  src := fun {n} _ => PUnit.unit
  tgt := fun {n} _ => PUnit.unit
  src_src_eq_src_tgt := by intro n x; rfl
  tgt_src_eq_tgt_tgt := by intro n x; rfl

def terminalOmega : StrictOmegaCategory where
  G := terminalGlobularSet
  idCell := by
    intro n a
    exact ⟨PUnit.unit, rfl, rfl⟩
  compCell := by
    intro n a b c f g
    exact ⟨PUnit.unit, rfl, rfl⟩
  id_comp := by
    intro n a b f
    cases f with
    | mk f hf =>
      cases f
      rfl
  comp_id := by
    intro n a b f
    cases f with
    | mk f hf =>
      cases f
      rfl
  assoc := by
    intro n a b c d f g h
    cases f with
    | mk f hf =>
      cases g with
      | mk g hg =>
        cases h with
        | mk h hh =>
          cases f
          cases g
          cases h
          rfl

def terminalNCat (n : Nat) : StrictNCat n :=
  { C := terminalOmega
    trunc := by
      intro m hm
      refine ⟨?_⟩
      intro a b
      cases a
      cases b
      rfl }

end Examples

end IteratedVirtual
end HeytingLean
