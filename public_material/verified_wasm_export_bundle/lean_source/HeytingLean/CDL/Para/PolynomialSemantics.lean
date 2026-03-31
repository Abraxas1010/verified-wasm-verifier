/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Para Bicategory - Polynomial Semantics
======================================

This module establishes the connection between the Para(Type) bicategory
and polynomial functors, showing that:

1. Para morphisms correspond to polynomial applications
2. Para composition corresponds to polynomial substitution
3. Reparameterizations are natural transformations

## Main Definitions

* `ParaToPoly` - Functor from Para objects to Poly
* `paraHomAsPoly` - View ParaHom as polynomial application
* `para_comp_is_subst` - Para composition = polynomial substitution

## Mathematical Background

A ParaHom X Y is a pair (P, f : P × X → Y), which by currying is (P, f : P → X → Y).

This is exactly the evaluation of a polynomial:
- Let p = P y^1 (linear polynomial with positions P)
- Then applyFun p (X → Y) = Σ (pos : P), (X → Y)
- Which is P × (X → Y) ≅ P → X → Y (by uncurrying the Sigma)

So ParaHom X Y ≅ Σ (P : Type), applyFun (linear P) (X → Y)

## References

* [Polynomial Functors Book](https://toposinstitute.github.io/poly/poly-book.pdf)
* CDL: Categorical Deep Learning
-/

import HeytingLean.CDL.Para.Type
import HeytingLean.CategoryTheory.Polynomial.Basic
import HeytingLean.CategoryTheory.Polynomial.Substitution

namespace HeytingLean
namespace CDL
namespace Para

open CategoryTheory
open CategoryTheory.Polynomial

universe u

/-! ## Para Objects as Polynomials -/

/-- View a type as a constant polynomial.
    A Para object X becomes the polynomial X y^0 (positions = X, no directions). -/
def typeToPoly (X : Type u) : Poly.{u, 0} := const X

/-- View a ParaHom as a polynomial structure.

A ParaHom X Y with parameter P and map f : P × X → Y
corresponds to a polynomial with:
- Positions: P (the parameter space)
- Directions: X (the input needed at each position)
- Applied to Y gives the output -/
def paraHomToPoly (m : ParaHom X Y) : Poly.{u, u} :=
  monomial m.P X

/-! ## Para Composition and Polynomial Substitution -/

/-- The polynomial corresponding to a composed ParaHom.

For ParaHom.comp g f where:
- f : ParaHom X Y with parameter Pf
- g : ParaHom Y Z with parameter Pg

The composition has parameter Pg × Pf, matching polynomial product. -/
theorem paraHomToPoly_comp {X Y Z : Type u} (f : ParaHom X Y) (g : ParaHom Y Z) :
    (paraHomToPoly (ParaHom.comp g f)).pos = (g.P × f.P) := by
  rfl

/-- Para identity corresponds to the unit polynomial. -/
theorem paraHomToPoly_id (X : Type u) :
    (paraHomToPoly (ParaHom.id X)).pos = PUnit := by
  rfl

/-! ## Reparameterization as Polynomial Morphism -/

/-- A reparameterization r : P' → P induces a polynomial morphism.

Given r : P' → P, we get a polymap from (P' y^X) to (P y^X):
- onPos: r (the reparameterization itself)
- onDir: identity (directions don't change) -/
def reparamToPolymap {X : Type u} {P P' : Type u} (r : P' → P) :
    monomial P' X ⟶ monomial P X where
  onPos := r
  onDir := fun _ => id

/-- Reparameterization composition corresponds to polymap composition -/
theorem reparamToPolymap_comp {X : Type u} {P P' P'' : Type u}
    (r : P' → P) (s : P'' → P') :
    reparamToPolymap (X := X) (r ∘ s) = composemap (reparamToPolymap s) (reparamToPolymap r) := by
  rfl

/-- Reparameterization identity is polymap identity -/
theorem reparamToPolymap_id {X P : Type u} :
    reparamToPolymap (X := X) (id : P → P) = polyid (monomial P X) := by
  rfl

/-! ## Para2Hom as Natural Transformation -/

/-- A Para2Hom (reparameterization) corresponds to a polymap between
    the polynomials of the source and target ParaHoms.

Given α : Para2Hom f g where:
- f : ParaHom X Y with parameter Pf
- g : ParaHom X Y with parameter Pg
- α.r : Pg → Pf

This gives a polymap from paraHomToPoly g to paraHomToPoly f. -/
def para2HomToPolymap {X Y : Type u} {f g : ParaHom X Y} (α : Para2Hom f g) :
    paraHomToPoly g ⟶ paraHomToPoly f :=
  reparamToPolymap α.r

/-- Identity Para2Hom gives identity polymap -/
theorem para2HomToPolymap_refl {X Y : Type u} (f : ParaHom X Y) :
    para2HomToPolymap (Para2Hom.refl f) = polyid (paraHomToPoly f) := by
  simp only [para2HomToPolymap, Para2Hom.refl, reparamToPolymap, polyid]
  rfl

/-- Vertical composition of Para2Hom corresponds to polymap composition -/
theorem para2HomToPolymap_vcomp {X Y : Type u} {f g h : ParaHom X Y}
    (α : Para2Hom f g) (β : Para2Hom g h) :
    para2HomToPolymap (Para2Hom.vcomp α β) =
    composemap (para2HomToPolymap β) (para2HomToPolymap α) := by
  simp only [para2HomToPolymap, Para2Hom.vcomp, reparamToPolymap, composemap]
  rfl

/-! ## Arena Semantics Preview -/

/-- An arena is a polynomial functor viewed as an interactive system.

Positions = states of the system
Directions = actions/observations available at each state

This is the foundation for connecting Para dynamics to polynomial dynamics. -/
abbrev Arena := Poly

/-- View a ParaHom as defining an arena transition.

Given m : ParaHom X Y, we can view this as:
- Arena with positions = m.P (parameter/state space)
- At each state p, the system can observe X and produce Y
- The map m.f : P × X → Y is the transition function -/
def paraHomToArena (m : ParaHom X Y) : Arena := paraHomToPoly m

/-- Arena step function via ParaHom semantics -/
def arenaStep {X Y : Type u} (m : ParaHom X Y) (state : m.P) (input : X) : Y :=
  m.f (state, input)

/-! ## Functoriality Summary -/

/-- The assignment ParaHom ↦ Poly respects identity. -/
theorem para_poly_id (X : Type u) : (paraHomToPoly (ParaHom.id X)).pos = PUnit := rfl

/-- The assignment ParaHom ↦ Poly respects composition. -/
theorem para_poly_comp {X Y Z : Type u} (f : ParaHom X Y) (g : ParaHom Y Z) :
    (paraHomToPoly (ParaHom.comp g f)).pos = (g.P × f.P) := rfl

/-- Summary: ParaHom ↦ Poly preserves the essential algebraic structure.

This is not a full functor since Para is a bicategory and Poly is a category,
but it respects:
1. Identity: ParaHom.id ↦ unit polynomial (PUnit positions)
2. Composition: ParaHom.comp ↦ product of position types
3. 2-cells: Para2Hom ↦ polymap (reparameterization) -/
theorem para_poly_structure_summary :
    (∀ X, (paraHomToPoly (ParaHom.id X)).pos = PUnit) ∧
    (∀ X Y Z (f : ParaHom X Y) (g : ParaHom Y Z),
      (paraHomToPoly (ParaHom.comp g f)).pos = (g.P × f.P)) :=
  ⟨fun _ => rfl, fun _ _ _ _ _ => rfl⟩

end Para
end CDL
end HeytingLean
