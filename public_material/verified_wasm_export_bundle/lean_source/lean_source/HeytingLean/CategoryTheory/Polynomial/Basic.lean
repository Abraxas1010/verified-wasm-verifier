/-
Copyright (c) 2023 David Spivak, Shaowei Lin. All rights reserved.
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Polynomial Functors - Basic Definitions
=======================================

This module provides the core definitions for polynomial functors, ported from
ToposInstitute/lean-poly with adaptations for HeytingLean's toolchain.

## Main Definitions

* `Poly` - A polynomial functor, given by positions and directions
* `polymap` - A lens/morphism between polynomial functors
* `Poly.category` - The category of polynomial functors

## References

* [Polynomial Functors Book](https://toposinstitute.github.io/poly/poly-book.pdf)
* [nLab: Polynomial functor](https://ncatlab.org/nlab/show/polynomial+functor)
* [ToposInstitute/lean-poly](https://github.com/ToposInstitute/lean-poly)
-/

import Mathlib.CategoryTheory.Category.Basic

universe u v w

namespace CategoryTheory

namespace Polynomial

set_option linter.dupNamespace false in
/-- A polynomial functor. Objects are pairs (pos, dir) where:
- `pos` is the type of positions (shapes)
- `dir` assigns a type of directions to each position

A polynomial P represents the functor P(X) = Σ (p : pos), X^(dir p) -/
structure Poly where
  /-- The type of positions (shapes) -/
  pos : Type u
  /-- The type of directions at each position -/
  dir : pos → Type v

/-- A lens/morphism between polynomial functors.
Given polynomials p and q, a lens consists of:
- `onPos`: a forward map on positions
- `onDir`: a backward map on directions -/
@[ext]
structure polymap (p q : Poly.{u, v}) : Type max u v where
  /-- Forward map on positions -/
  onPos : p.pos → q.pos
  /-- Backward map on directions -/
  onDir : (x : p.pos) → q.dir (onPos x) → p.dir x

/-- The identity lens from a polynomial to itself -/
def polyid (p : Poly) : polymap p p where
  onPos := id
  onDir := fun _ => id

/-- Composition of lenses in diagrammatic order -/
def composemap {p q r : Poly} (f : polymap p q) (g : polymap q r) :
    polymap p r where
  onPos := g.onPos ∘ f.onPos
  onDir := fun px rd => f.onDir px (g.onDir (f.onPos px) rd)

/-- Poly as a type with categorical structure -/
instance Poly.categoryStruct : CategoryStruct Poly where
  Hom := polymap
  id := polyid
  comp := composemap

/-- Poly forms a category -/
instance Poly.category : Category Poly where
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- Apply a polynomial functor to get a type -/
def applyFun (p : Poly.{u, v}) (T : Type w) : Type max u v w :=
  Σ (x : p.pos), (p.dir x) → T

/-- Apply a lens to get a function between applied types -/
def applyMap {p q : Poly.{u, v}} (f : p ⟶ q) (T : Type w) :
    (applyFun p T) → (applyFun q T) :=
  fun x => Sigma.mk (f.onPos x.fst) (x.snd ∘ (f.onDir x.fst))

/-!
## Special Polynomial Functors
-/

/-- A monomial functor with constant direction type -/
def monomial (P : Type u) (D : Type v) : Poly.{u, v} where
  pos := P
  dir := fun _ => D

/-- Notation for a monomial functor: A y^B -/
scoped notation:80 A:80 " y^" B:80 => monomial A B

/-- A representable functor y^D -/
def representable (D : Type v) : Poly.{u, v} := PUnit.{u+1} y^D

/-- Notation for a representable functor -/
scoped notation:80 "y^" B:80 => representable B

/-- A constant polynomial functor -/
def const (P : Type u) : Poly.{u, v} := P y^(PEmpty.{v+1})

/-- Notation for constant polynomial: A y^0 -/
scoped notation:80 A:80 " y^0" => const A

/-- A linear polynomial functor -/
def linear (P : Type u) : Poly.{u, v} := P y^(PUnit.{v+1})

/-- Notation for linear polynomial: A y^1 -/
scoped notation:80 A:80 " y^1" => linear A

/-- The identity polynomial functor -/
def y : Poly.{u, v} := linear PUnit.{u+1}

/-- Alternative notation for y -/
scoped notation "y^1" => y

/-- The initial object in Poly -/
def poly0 : Poly.{u, v} := const PEmpty.{u+1}

/-- Notation for initial object: 𝟬 -/
scoped notation "𝟬" => poly0

/-- Notation for the unique map from empty -/
scoped notation "!𝟬" => PEmpty.rec

/-- The terminal object in Poly -/
def poly1 : Poly.{u, v} := const PUnit.{u+1}

/-- Notation for terminal object: 𝟭 -/
scoped notation "𝟭" => poly1

/-- Notation for the unique map to unit -/
scoped notation "!𝟭" => Function.const _ PUnit.unit

/-!
## Special Lenses
-/

/-- A lens between constant polynomial functors -/
def constantMap {T T' : Type u} (f : T → T') : T y^0 ⟶ T' y^0 where
  onPos := f
  onDir := fun _ => !𝟬

/-- A lens between linear polynomial functors -/
def linearMap {T T' : Type u} (f : T → T') : T y^1 ⟶ T' y^1 where
  onPos := f
  onDir := fun _ => !𝟭

/-- A lens between representable functors (contravariant in direction) -/
def representableMap {T T' : Type u} (f : T → T') : y^T' ⟶ y^T where
  onPos := !𝟭
  onDir := fun _ => f

/-- The unique lens from the initial object -/
def bang0poly {p : Poly.{u, v}} : 𝟬 ⟶ p where
  onPos := !𝟬
  onDir := !𝟬

/-- The unique lens to the terminal object -/
def bang1poly {p : Poly.{u, v}} : p ⟶ 𝟭 where
  onPos := !𝟭
  onDir := fun _ => !𝟬

/-- Alternative representation for lenses using sigma types -/
def polymap2 (p q : Poly.{u, v}) : Type max u v :=
  (px : p.pos) → Σ (qx : q.pos), q.dir qx → p.dir px

/-- Cast from polymap to polymap2 -/
def cast12 {p q : Poly.{u, v}} (f : p ⟶ q) : polymap2 p q :=
  fun px => Sigma.mk (f.onPos px) (f.onDir px)

/-- Cast from polymap2 to polymap -/
def cast21 {p q : Poly.{u, v}} (f : polymap2 p q) : p ⟶ q where
  onPos := fun px => (f px).fst
  onDir := fun px => (f px).snd

end Polynomial

end CategoryTheory
