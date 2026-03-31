import Mathlib.Order.Hom.BoundedLattice
import Mathlib.CategoryTheory.Category.Basic
import HeytingLean.Quantum.OML.Core

/-
# OMLCat: category of orthomodular lattices

This module bundles the project’s orthomodular lattice structure into a small
category `OMLCat`.  Objects are types equipped with an
`OrthocomplementedLattice` and `OrthomodularLattice` instance; morphisms are
bounded lattice homomorphisms that additionally preserve the orthocomplement.

For now we keep the interface intentionally light:

* `OMLCat` – bundled object;
* `OMLCat.Hom` – complement-preserving bounded lattice homs;
* `Category OMLCat` – with the obvious identity and composition.

Later Direction‑6 files (vacuum naturality) will use this as the domain for
functors out of the OML layer.
-/

namespace HeytingLean
namespace Quantum

open HeytingLean.Quantum.OML
open CategoryTheory

universe u

/-- Bundled orthomodular lattice, for categorical use. -/
structure OMLCat where
  carrier : Type u
  [isOrthocompl : OrthocomplementedLattice carrier]
  [isOrthomod   : OrthomodularLattice carrier]

attribute [instance] OMLCat.isOrthocompl
attribute [instance] OMLCat.isOrthomod

namespace OMLCat

instance : CoeSort OMLCat (Type u) :=
  ⟨fun X => X.carrier⟩

attribute [coe] OMLCat.carrier

/-- Convenient constructor from a type equipped with the required structures. -/
abbrev of (α : Type u) [OrthocomplementedLattice α] [OrthomodularLattice α] :
    OMLCat :=
  ⟨α⟩

/-- Morphisms in `OMLCat`: bounded lattice homomorphisms that also preserve the
orthocomplement. -/
@[ext]
structure Hom (X Y : OMLCat.{u}) where
  private mk ::
  /-- Underlying bounded lattice homomorphism. -/
  hom' : BoundedLatticeHom X Y
  /-- Compatibility with the orthocomplement. -/
  map_compl' :
    ∀ a : X,
      hom' (OrthocomplementedLattice.compl a)
        = OrthocomplementedLattice.compl (hom' a)

/-- Underlying function of an `OMLCat.Hom`. -/
instance (X Y : OMLCat.{u}) : CoeFun (Hom X Y) (fun _ => X → Y) :=
  ⟨fun f => f.hom'⟩

/-- Turn a morphism in `OMLCat` back into a `BoundedLatticeHom`. -/
abbrev Hom.toBoundedLatticeHom {X Y : OMLCat.{u}} (f : Hom X Y) :
    BoundedLatticeHom X Y :=
  f.hom'

@[simp] lemma hom_apply {X Y : OMLCat} (f : Hom X Y) (x : X) :
    f x = f.hom' x := rfl

@[simp] lemma map_compl (f : Hom X Y) (a : X) :
    f (OrthocomplementedLattice.compl a)
      = OrthocomplementedLattice.compl (f a) :=
  f.map_compl' a

/-- Identity morphism in `OMLCat`. -/
def id (X : OMLCat) : Hom X X :=
  { hom' := BoundedLatticeHom.id X
    map_compl' := by
      intro a
      -- `BoundedLatticeHom.id` is literally the identity.
      rfl }

/-- Composition of morphisms in `OMLCat`. -/
def comp {X Y Z : OMLCat} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  { hom' := g.hom'.comp f.hom'
    map_compl' := by
      intro a
      -- expand the composite on complements and use the component laws.
      change g.hom' (f.hom' (OrthocomplementedLattice.compl a))
        = _
      -- first push complement through `f`, then through `g`
      simpa [BoundedLatticeHom.comp_apply, map_compl] }

@[simp] lemma id_apply (X : OMLCat) (x : X) :
    id X x = x := rfl

@[simp] lemma comp_apply {X Y Z : OMLCat}
    (f : Hom X Y) (g : Hom Y Z) (x : X) :
    comp f g x = g (f x) := rfl

instance : Category OMLCat where
  Hom X Y := Hom X Y
  id X := id X
  comp f g := comp f g

end OMLCat

end Quantum
end HeytingLean
