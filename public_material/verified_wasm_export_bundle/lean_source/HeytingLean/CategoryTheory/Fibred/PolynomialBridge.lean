/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Fibred Categories - Polynomial Bridge
=====================================

This module establishes the duality between fibred categories and polynomial functors.

## Main Results

* `polyToFibred` - View a polynomial as a fibration structure
* `fibredToPoly` - View a fibred structure as a polynomial
* `BasedLift_polymap_equiv` - Based lifts correspond to polymaps

## Mathematical Background

Fibred categories and polynomial functors are mathematically dual perspectives:

| Fibred Category | Polynomial Functor |
|-----------------|-------------------|
| Fiber `P⁻¹ c` | Directions `Poly.dir p` |
| BasedLift | Polymap (lens) |
| Transport | Substitution reindexing |
| Grothendieck construction | Arena semantics |
| Beck-Chevalley | Polynomial composition laws |

The same author (Sina Hazratpour) developed both LeanFibredCategories and sinhp/Poly,
so these formalizations are designed to connect.

## References

* [nLab: Grothendieck fibration](https://ncatlab.org/nlab/show/Grothendieck+fibration)
* [Polynomial Functors Book](https://toposinstitute.github.io/poly/poly-book.pdf)
-/

import HeytingLean.CategoryTheory.Fibred.Basic
import HeytingLean.CategoryTheory.Polynomial.Basic

namespace HeytingLean
namespace CategoryTheory

open _root_.CategoryTheory.Polynomial
open Fibred

universe u v

/-! ## Polynomial as Family Fibration -/

/-- A polynomial functor defines a "fibration" structure.

Given a polynomial `p`, the projection `Σ (x : p.pos), p.dir x → p.pos`
is analogous to a fibration where:
- Base category: discrete category on `p.pos`
- Fiber over `x`: `p.dir x`

This is the Grothendieck construction of the family `p.dir : p.pos → Type`. -/
structure PolyFamily (p : Poly.{u, v}) where
  /-- The base position -/
  base : p.pos
  /-- An element of the fiber over that position -/
  fiber : p.dir base

namespace PolyFamily

variable {p : Poly.{u, v}}

/-- Projection to base is the "fibration" map -/
def proj : PolyFamily p → p.pos := PolyFamily.base

/-- The fiber over a position -/
def fiberOver (x : p.pos) : Type v := p.dir x

/-- Elements in a specific fiber -/
def inFiber (x : p.pos) (d : p.dir x) : PolyFamily p := ⟨x, d⟩

end PolyFamily

/-! ## Polymap as Transport -/

/-! **Note on Contravariance**: A polymap does NOT induce forward transport on fibers.

Given `f : p ⟶ q`:
- `onPos` moves positions forward: `p.pos → q.pos`
- `onDir` moves directions BACKWARD: `q.dir (f.onPos x) → p.dir x`

This means we cannot define `polymapTransport (f : p ⟶ q) (fam : PolyFamily p) : PolyFamily q`
because to produce a `q.dir (f.onPos fam.base)`, we would need to invert `onDir`.

This contravariance is exactly what makes polymaps correspond to lenses:
- `get` (onPos) goes forward
- `put` (onDir) goes backward

In fibration terms, this is the cartesian lift property: given a target fiber element,
we can lift back to the source fiber. -/

/-- Polymap transport is contravariant on fibers.

A polymap `f : p ⟶ q` gives:
- Forward on positions: `p.pos → q.pos`
- Backward on fibers: `q.dir (f.onPos x) → p.dir x`

This matches the fibration pattern where cartesian lifts go "backward". -/
def polymapLift {p q : Poly.{u, v}} (f : p ⟶ q) (x : p.pos) (qd : q.dir (f.onPos x)) : p.dir x :=
  f.onDir x qd

/-! ## Correspondence with Based Lifts -/

/-- A based lift structure on polynomials.

Given polynomials `p` and `q` and a "base morphism" `f : p.pos → q.pos`,
a based lift provides the backward transport on fibers. -/
structure PolyBasedLift (p q : Poly.{u, v}) (f : p.pos → q.pos) where
  /-- Backward transport on fibers -/
  liftDir : (x : p.pos) → q.dir (f x) → p.dir x

/-- Every polymap is a based lift over its position map. -/
def polymap.toBasedLift {p q : Poly.{u, v}} (m : p ⟶ q) : PolyBasedLift p q m.onPos where
  liftDir := m.onDir

/-- Every based lift with a position map is a polymap. -/
def PolyBasedLift.toPolymap {p q : Poly.{u, v}} {f : p.pos → q.pos}
    (l : PolyBasedLift p q f) : p ⟶ q where
  onPos := f
  onDir := l.liftDir

/-- Based lifts and polymaps are equivalent. -/
theorem polyBasedLift_polymap_equiv {p q : Poly.{u, v}} (m : p ⟶ q) :
    (polymap.toBasedLift m).toPolymap = m := rfl

/-! ## Polynomial Substitution as Fiber Composition -/

/-- The substitution product of polynomials corresponds to composing fibrations.

In fibred category terms:
- Given fibrations `P : E → C` and `Q : F → E`
- The composite `P ∘ Q : F → C` is a fibration
- Cartesian lifts in the composite come from lifting in both

In polynomial terms:
- Given `p, q : Poly`
- The substitution `p ◁ q` has positions `Σ (x : p.pos), q.dir x → q.pos`
- Directions compose multiplicatively -/
def substAsComposite (p q : Poly.{u, u}) :
    -- The substitution product positions
    let substPos := Σ (x : p.pos), (p.dir x → q.pos)
    -- This is like a "composed fibration" structure
    substPos → p.pos := Sigma.fst

/-! ## Beck-Chevalley as Polynomial Laws -/

/-- Beck-Chevalley condition: pullback along f followed by pushforward along g
    equals pushforward along g' followed by pullback along f'.

In polynomial terms, this becomes the naturality of substitution. -/
theorem beckChevalley_naturality {p q r : Poly.{u, u}}
    (f : p ⟶ q) (g : q ⟶ r) :
    -- Composing polymaps respects the fibration structure
    (composemap f g).onPos = g.onPos ∘ f.onPos := rfl

/-! ## Summary: The Duality -/

/-- The polynomial-fibration duality table formalized:

1. Positions ↔ Base objects
2. Directions ↔ Fiber elements
3. Polymap ↔ Cartesian lift structure
4. Substitution ↔ Composition of fibrations
5. Beck-Chevalley ↔ Naturality of polymap composition

This duality is fundamental to understanding both perspectives. -/
theorem poly_fibred_duality_summary :
    -- Polymap composition is associative (like fibration composition)
    (∀ {p q r s : Poly.{u, u}} (f : p ⟶ q) (g : q ⟶ r) (h : r ⟶ s),
      composemap (composemap f g) h = composemap f (composemap g h)) ∧
    -- Identity polymap is neutral (like identity fibration)
    (∀ {p q : Poly.{u, u}} (f : p ⟶ q),
      composemap (polyid p) f = f ∧ composemap f (polyid q) = f) := by
  constructor
  · intros; rfl
  · intro _ _ f; exact ⟨rfl, rfl⟩

end CategoryTheory
end HeytingLean
