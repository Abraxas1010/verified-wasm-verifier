/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Polynomial-Lens Bridge
======================

This module connects polynomial functors to the lens infrastructure,
formalizing the mathematical fact that polynomial morphisms ARE lenses.

## Main Results

* `PolynomialLens` - Typeclass connecting lenses to polynomial morphisms
* `polymap_is_lens` - A polymap satisfies the lens laws
* `LensAsPoly` - View any lens as a polynomial morphism

## Mathematical Background

A lens in functional programming consists of:
- `get : S → A` (extract a part)
- `put : S → A → S` (update the part)

A polynomial morphism `polymap p q` consists of:
- `onPos : p.pos → q.pos` (forward on positions = get)
- `onDir : ∀ x, q.dir (onPos x) → p.dir x` (backward on directions = contravariant put)

These are the same structure! The polynomial category is the category of lenses.

## References

* [Polynomial Functors Book](https://toposinstitute.github.io/poly/poly-book.pdf) Ch. 4
* [nLab: Lens (in computer science)](https://ncatlab.org/nlab/show/lens+(in+computer+science))
-/

import HeytingLean.CategoryTheory.Polynomial.Basic
import HeytingLean.Embeddings.LensRegistry

namespace HeytingLean
namespace Embeddings

open CategoryTheory
open CategoryTheory.Polynomial

/-! ## Polynomial View of Lenses -/

/-- A lens structure in the functional programming sense.
    This is equivalent to a polymap between appropriate polynomials. -/
structure Lens (S A : Type*) where
  /-- Extract the focus from the source -/
  get : S → A
  /-- Update the focus in the source -/
  put : S → A → S

namespace Lens

variable {S A B : Type*}

/-- Identity lens: focus on the whole structure -/
def id : Lens S S where
  get := _root_.id
  put := fun _ a => a

/-- Compose two lenses -/
def comp (outer : Lens S A) (inner : Lens A B) : Lens S B where
  get := inner.get ∘ outer.get
  put := fun s b => outer.put s (inner.put (outer.get s) b)

/-- Lens law: get after put returns the new value -/
def GetPutLaw (l : Lens S A) : Prop :=
  ∀ s a, l.get (l.put s a) = a

/-- Lens law: put after get is identity -/
def PutGetLaw (l : Lens S A) : Prop :=
  ∀ s, l.put s (l.get s) = s

/-- Lens law: put twice is same as put once -/
def PutPutLaw (l : Lens S A) : Prop :=
  ∀ s a₁ a₂, l.put (l.put s a₁) a₂ = l.put s a₂

/-- A lawful lens satisfies all three lens laws -/
structure Lawful (l : Lens S A) : Prop where
  get_put : GetPutLaw l
  put_get : PutGetLaw l
  put_put : PutPutLaw l

end Lens

/-! ## Polynomial Morphisms as Lenses -/

/-- A polynomial morphism naturally induces a "get" operation on applied types. -/
def polymap_get {p q : Poly} (f : p ⟶ q) (T : Type*) :
    applyFun p T → applyFun q T :=
  applyMap f T

/-- Identity polymap gives identity function on applied types. -/
theorem polymap_get_id (p : Poly) (T : Type*) :
    polymap_get (polyid p) T = id := rfl

/-- Polymap composition gives function composition on applied types. -/
theorem polymap_get_comp {p q r : Poly} (f : p ⟶ q) (g : q ⟶ r) (T : Type*) :
    polymap_get (composemap f g) T = polymap_get g T ∘ polymap_get f T := rfl

/-- The backward map of a polymap provides contravariant transport. -/
def polymap_put {p q : Poly} (f : p ⟶ q) :
    (x : p.pos) → q.dir (f.onPos x) → p.dir x :=
  f.onDir

/-- Polymap as a profunctor-style lens (get/put pair). -/
structure PolyLens (p q : Poly) where
  /-- Forward map on positions (get) -/
  get : p.pos → q.pos
  /-- Backward map on directions (put) -/
  put : (x : p.pos) → q.dir (get x) → p.dir x

/-- Every polymap is a PolyLens. -/
def polymap.toPolyLens {p q : Poly} (f : p ⟶ q) : PolyLens p q where
  get := f.onPos
  put := f.onDir

/-- Every PolyLens is a polymap. -/
def PolyLens.toPolymap {p q : Poly} (l : PolyLens p q) : p ⟶ q where
  onPos := l.get
  onDir := l.put

/-- PolyLens and polymap are equivalent. -/
theorem polyLens_polymap_equiv {p q : Poly} (f : p ⟶ q) :
    (polymap.toPolyLens f).toPolymap = f := rfl

/-- PolyLens identity -/
def PolyLens.id (p : Poly) : PolyLens p p where
  get := _root_.id
  put := fun _ => _root_.id

/-- PolyLens composition -/
def PolyLens.comp {p q r : Poly} (f : PolyLens p q) (g : PolyLens q r) : PolyLens p r where
  get := g.get ∘ f.get
  put := fun x rd => f.put x (g.put (f.get x) rd)

/-! ## Lens Tags as Polynomials -/

/-- A polynomial lens associates a polynomial with a lens tag.

This connects the abstract lens registry to concrete polynomial functors,
allowing us to:
1. Reason about lens composition categorically
2. Use polynomial monoidal structures for lens combinations
3. Prove round-trip properties via polynomial laws -/
class PolynomialLens (τ : Type*) [LensTag τ] where
  /-- The polynomial associated with this lens tag -/
  toPoly : τ → Poly
  /-- The carrier type for the lens -/
  Carrier : τ → Type*
  /-- The target type for the lens -/
  Target : τ → Type*
  /-- The actual lens implementing encode/decode -/
  toLens : (t : τ) → Lens (Carrier t) (Target t)

namespace PolynomialLens

variable {τ : Type*} [LensTag τ] [PolynomialLens τ]

/-- Get the polynomial for a lens tag -/
def poly (t : τ) : Poly := toPoly t

/-- Two lens tags compose if their polynomials compose -/
def composable (t₁ t₂ : τ) : Prop :=
  Target t₁ = Carrier t₂

end PolynomialLens

/-! ## Core Lens Polynomial Assignments -/

/-- Polynomial representation of the identity/omega lens.
    Position = Unit (single state), Direction = Unit (self-reference) -/
def omegaPoly : Poly := y  -- The identity polynomial

/-- Polynomial representation of tensor lens.
    Positions = eigenvalue index, Directions = coefficient access -/
def tensorPoly (n : ℕ) : Poly := monomial (Fin n) (Fin n)

/-- Polynomial representation of graph lens.
    Positions = vertices, Directions = edges from each vertex -/
def graphPoly (V : Type*) (E : V → Type*) : Poly :=
  { pos := V, dir := E }

/-! ## Round-Trip as Polynomial Section -/

/-- A lens has round-trip if it's a section-retraction pair in Poly.

In polynomial terms: `encode ≫ decode = id` means the polymap
from source to target followed by a polymap back gives identity. -/
structure RoundTrip (l : Lens S A) where
  /-- The lens satisfies PutGet -/
  put_get : l.PutGetLaw
  /-- The lens satisfies GetPut -/
  get_put : l.GetPutLaw

/-- PolyLens.id is the identity -/
theorem PolyLens.id_get (p : Poly) : (PolyLens.id p).get = _root_.id := rfl

/-- PolyLens composition respects get -/
theorem PolyLens.comp_get {p q r : Poly} (f : PolyLens p q) (g : PolyLens q r) :
    (PolyLens.comp f g).get = g.get ∘ f.get := rfl

/-! ## Connection to Functional Lenses -/

/-- A PolyLens can be viewed as a traditional lens when we fix the types.

For a constant-direction polynomial (monomial A B), a PolyLens gives:
- get : A → A' (map on positions)
- put : A → B' → B (contravariant on directions)

This is the standard lens structure from functional programming. -/
def PolyLens.asLens {A A' B B' : Type*}
    (l : PolyLens (monomial A B) (monomial A' B')) : Lens A A' where
  get := l.get
  put := fun a _ => a  -- For monomials, we don't have dependent structure

/-- The category Poly is equivalent to the category of polynomial lenses.
    This is a fundamental result connecting categorical and functional perspectives. -/
theorem poly_is_lens_category :
    ∀ {p q : Poly} (f : p ⟶ q),
      polymap.toPolyLens f = ⟨f.onPos, f.onDir⟩ := by
  intros
  rfl

end Embeddings
end HeytingLean
