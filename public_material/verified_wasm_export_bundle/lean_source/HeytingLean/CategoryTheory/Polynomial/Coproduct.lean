/-
Copyright (c) 2023 David Spivak, Shaowei Lin. All rights reserved.
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Polynomial Functors - Coproduct
===============================

Coproduct (sum) and product of polynomial functors.

## Main Definitions

* `coproduct` - Coproduct p + q
* `product` - Cartesian product p × q (with direction sum)
* `orProd` - Or product p ∨ q

## References

* [Polynomial Functors Book](https://toposinstitute.github.io/poly/poly-book.pdf)
-/

import HeytingLean.CategoryTheory.Polynomial.Basic

namespace CategoryTheory

namespace Polynomial

open Polynomial

/-!
## Coproduct
-/

/-- Coproduct of polynomial functors -/
def coproduct (p q : Poly.{u, u}) : Poly.{u, u} where
  pos := p.pos ⊕ q.pos
  dir := fun x =>
    match x with
    | .inl ppos => p.dir ppos
    | .inr qpos => q.dir qpos

/-- Notation for coproduct -/
scoped infixr:75 " +ᵖ " => coproduct

/-- Bifunctorial action of coproduct on morphisms -/
def coproduct.map {p q r z : Poly.{u, u}} (f : p ⟶ q) (g : r ⟶ z) :
    (p +ᵖ r) ⟶ (q +ᵖ z) where
  onPos := fun pos =>
    match pos with
    | .inl ppos => .inl (f.onPos ppos)
    | .inr qpos => .inr (g.onPos qpos)
  onDir := fun pos =>
    match pos with
    | .inl ppos => f.onDir ppos
    | .inr rpos => g.onDir rpos

/-- Whisker coproduct on the left -/
def coproduct.whiskerLeft (p : Poly) {q q' : Poly} (f : q ⟶ q') :
    (p +ᵖ q) ⟶ (p +ᵖ q') :=
  coproduct.map (𝟙 p) f

/-- Whisker coproduct on the right -/
def coproduct.whiskerRight {p p' : Poly} (f : p ⟶ p') (q : Poly) :
    (p +ᵖ q) ⟶ (p' +ᵖ q) :=
  coproduct.map f (𝟙 q)

/-- Left injection into coproduct -/
def coproduct.inl {p q : Poly.{u, u}} : p ⟶ (p +ᵖ q) where
  onPos := .inl
  onDir := fun _ => id

/-- Right injection into coproduct -/
def coproduct.inr {p q : Poly.{u, u}} : q ⟶ (p +ᵖ q) where
  onPos := .inr
  onDir := fun _ => id

/-- Left unitor hom: 𝟬 + p → p -/
def coproduct.leftUnitor.hom (p : Poly) : (poly0 +ᵖ p) ⟶ p where
  onPos := fun pos =>
    match pos with
    | .inr ppos => ppos
  onDir := fun pos dir =>
    match pos with
    | .inr _ => dir

/-- Inverse of left unitor: p → 𝟬 + p -/
def coproduct.leftUnitor.inv (p : Poly) : p ⟶ (poly0 +ᵖ p) where
  onPos := fun ppos => .inr ppos
  onDir := fun _ pdir => pdir

/-!
## Cartesian Product
-/

/-- Cartesian product of polynomial functors.
Note: directions are sums, not products (unlike tensor). -/
def product (p q : Poly.{u, u}) : Poly.{u, u} where
  pos := p.pos × q.pos
  dir := fun (ppos, qpos) => Sum (p.dir ppos) (q.dir qpos)

/-- Notation for cartesian product -/
scoped infixr:85 " ×ᵖ " => product

/-- Bifunctorial action of product on morphisms -/
def product.map {p q r z : Poly.{u, u}} (f : p ⟶ q) (g : r ⟶ z) :
    (p ×ᵖ r) ⟶ (q ×ᵖ z) where
  onPos := fun (ppos, rpos) => (f.onPos ppos, g.onPos rpos)
  onDir := fun (ppos, rpos) dir =>
    match dir with
    | .inl qdir => .inl (f.onDir ppos qdir)
    | .inr zdir => .inr (g.onDir rpos zdir)

/-- Whisker product on the left -/
def product.whiskerLeft (p : Poly) {q q' : Poly} (f : q ⟶ q') :
    (p ×ᵖ q) ⟶ (p ×ᵖ q') :=
  product.map (𝟙 p) f

/-- Whisker product on the right -/
def product.whiskerRight {p p' : Poly} (f : p ⟶ p') (q : Poly) :
    (p ×ᵖ q) ⟶ (p' ×ᵖ q) :=
  product.map f (𝟙 q)

/-- First projection from product -/
def product.fst {p q : Poly} : (p ×ᵖ q) ⟶ p where
  onPos := fun (ppos, _) => ppos
  onDir := fun _ pdir => .inl pdir

/-- Second projection from product -/
def product.snd {p q : Poly} : (p ×ᵖ q) ⟶ q where
  onPos := fun (_, qpos) => qpos
  onDir := fun _ qdir => .inr qdir

/-- Swap for product -/
def product.swap {p q : Poly} : (p ×ᵖ q) ⟶ (q ×ᵖ p) where
  onPos := fun (ppos, qpos) => (qpos, ppos)
  onDir := fun _ dir =>
    match dir with
    | .inl qdir => .inr qdir
    | .inr pdir => .inl pdir

/-- Diagonal/duplication for product -/
def product.dupe {p : Poly} : p ⟶ (p ×ᵖ p) where
  onPos := fun ppos => (ppos, ppos)
  onDir := fun _ dir =>
    match dir with
    | .inl pdir => pdir
    | .inr pdir => pdir

/-- Fan-out: given f : r → p and g : r → q, get r → p × q -/
def product.fanout {p q r : Poly} (f : r ⟶ p) (g : r ⟶ q) : r ⟶ (p ×ᵖ q) where
  onPos := fun rpos => (f.onPos rpos, g.onPos rpos)
  onDir := fun rpos dir =>
    match dir with
    | .inl pdir => f.onDir rpos pdir
    | .inr qdir => g.onDir rpos qdir

/-- Left unitor hom: 𝟭 × p → p -/
def product.leftUnitor.hom (p : Poly) : (poly1 ×ᵖ p) ⟶ p where
  onPos := fun ⟨_, ppos⟩ => ppos
  onDir := fun ⟨_, _⟩ pdir => .inr pdir

/-- Inverse of left unitor: p → 𝟭 × p -/
def product.leftUnitor.inv (p : Poly) : p ⟶ (poly1 ×ᵖ p) where
  onPos := fun ppos => (PUnit.unit, ppos)
  onDir := fun _ dir =>
    match dir with
    | .inr pfib => pfib

/-!
## Or Product (This/That/These)
-/

/-- Or product: p ∨ q = p + (p × q) + q -/
def orProd (p q : Poly.{u, u}) : Poly.{u, u} := p +ᵖ (p ×ᵖ q) +ᵖ q

/-- Notation for or product -/
scoped infixr:75 " ∨ᵖ " => orProd

/-- This injection: p → p ∨ q -/
def orProd.this {p q : Poly} : p ⟶ (p ∨ᵖ q) where
  onPos := .inl
  onDir := fun _ => id

/-- That injection: q → p ∨ q -/
def orProd.that {p q : Poly} : q ⟶ (p ∨ᵖ q) where
  onPos := .inr ∘ .inr
  onDir := fun _ => id

/-- These injection: p × q → p ∨ q -/
def orProd.these {p q : Poly} : (p ×ᵖ q) ⟶ (p ∨ᵖ q) where
  onPos := .inr ∘ .inl
  onDir := fun _ => id

/-- Eliminator for or product -/
def orProd.elim {p q r : Poly} (f : p ⟶ r) (g : q ⟶ r) (h : (p ×ᵖ q) ⟶ r) :
    (p ∨ᵖ q) ⟶ r where
  onPos := fun pos =>
    match pos with
    | .inl ppos => f.onPos ppos
    | .inr (.inl (ppos, qpos)) => h.onPos (ppos, qpos)
    | .inr (.inr qpos) => g.onPos qpos
  onDir := fun pos fib =>
    match pos with
    | .inl ppos => f.onDir ppos fib
    | .inr (.inl (ppos, qpos)) => h.onDir (ppos, qpos) fib
    | .inr (.inr qpos) => g.onDir qpos fib

end Polynomial

end CategoryTheory
