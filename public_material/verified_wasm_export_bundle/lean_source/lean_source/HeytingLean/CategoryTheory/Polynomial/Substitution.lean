/-
Copyright (c) 2023 David Spivak, Shaowei Lin. All rights reserved.
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Polynomial Functors - Substitution Product
==========================================

The substitution product makes Poly a monoidal category with unit y.

## Main Definitions

* `subst` - Substitution product p ◁ q
* `Poly.subst.monoidal` - Monoidal category structure

## References

* [Polynomial Functors Book](https://toposinstitute.github.io/poly/poly-book.pdf)
-/

import HeytingLean.CategoryTheory.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Category

namespace CategoryTheory

namespace Polynomial

open Polynomial

/-!
## Substitution Product
-/

/-- Substitution product of polynomial functors.
For polynomials in Poly.{u, u}, the product remains in Poly.{u, u}. -/
def subst (p q : Poly.{u, u}) : Poly.{u, u} where
  pos := applyFun p q.pos
  dir := fun x => Σ (d : p.dir x.fst), (q.dir (x.snd d))

/-- Notation for substitution product -/
scoped infixr:80 "◁" => subst

/-- Whisker a substitution product on the left -/
def subst.whiskerLeft (p : Poly) {q q' : Poly} (f : q ⟶ q') :
    (p ◁ q) ⟶ (p ◁ q') where
  onPos := fun x => Sigma.mk x.fst (f.onPos ∘ x.snd)
  onDir := fun x d => Sigma.mk d.fst (f.onDir (x.snd d.fst) d.snd)

/-- Whisker a substitution product on the right -/
def subst.whiskerRight {p p' : Poly} (f : p ⟶ p') (q : Poly) :
    (p ◁ q) ⟶ (p' ◁ q) where
  onPos := applyMap f q.pos
  onDir := fun x d => Sigma.mk (f.onDir x.fst d.fst) d.snd

/-- Left unitor for substitution: y ◁ p ≅ p -/
def subst.leftUnitor.hom (p : Poly) : (y ◁ p) ⟶ p where
  onPos := fun x => x.snd x.fst
  onDir := fun _ d => Sigma.mk PUnit.unit d

/-- Inverse of left unitor -/
def subst.leftUnitor.inv (p : Poly) : p ⟶ (y ◁ p) where
  onPos := fun x => Sigma.mk PUnit.unit (fun _ => x)
  onDir := fun _ d => d.snd

/-- Left unitor isomorphism -/
def subst.leftUnitor (p : Poly) : (y ◁ p) ≅ p where
  hom := subst.leftUnitor.hom p
  inv := subst.leftUnitor.inv p

/-- Right unitor for substitution: p ◁ y ≅ p -/
def subst.rightUnitor.hom (p : Poly) : (p ◁ y) ⟶ p where
  onPos := fun x => x.fst
  onDir := fun _ d => Sigma.mk d PUnit.unit

/-- Inverse of right unitor -/
def subst.rightUnitor.inv (p : Poly) : p ⟶ (p ◁ y) where
  onPos := fun x => Sigma.mk x (fun _ => PUnit.unit)
  onDir := fun _ d => d.fst

/-- Right unitor isomorphism -/
def subst.rightUnitor (p : Poly) : (p ◁ y) ≅ p where
  hom := subst.rightUnitor.hom p
  inv := subst.rightUnitor.inv p

/-- Associator for substitution: (p ◁ q) ◁ r ≅ p ◁ (q ◁ r) -/
def subst.associator.hom (p q r : Poly) : (p ◁ q) ◁ r ⟶ p ◁ (q ◁ r) where
  onPos := fun pq_r =>
    let pq_r1 := pq_r.fst
    let pq_r2 := pq_r.snd
    let pq_r11 := pq_r1.fst
    let pq_r12 := pq_r1.snd
    Sigma.mk pq_r11 (fun pd =>
      Sigma.mk (pq_r12 pd) (fun qd => pq_r2 (Sigma.mk pd qd)))
  onDir := fun _ p_qr =>
    let p_qr1 := p_qr.fst
    let p_qr2 := p_qr.snd
    let p_qr21 := p_qr2.fst
    let p_qr22 := p_qr2.snd
    Sigma.mk (Sigma.mk p_qr1 p_qr21) p_qr22

/-- Inverse of associator -/
def subst.associator.inv (p q r : Poly) : p ◁ (q ◁ r) ⟶ (p ◁ q) ◁ r where
  onPos := fun p_qr =>
    let p_qr1 := p_qr.fst
    let p_qr2 := p_qr.snd
    Sigma.mk (Sigma.mk p_qr1 (fun pd => (p_qr2 pd).fst))
             (fun pqd => (p_qr2 pqd.fst).snd pqd.snd)
  onDir := fun _ pq_rd =>
    let pq_rd1 := pq_rd.fst
    let pq_rd2 := pq_rd.snd
    Sigma.mk pq_rd1.fst (Sigma.mk pq_rd1.snd pq_rd2)

/-- Associator isomorphism -/
def subst.associator (p q r : Poly) : (p ◁ q) ◁ r ≅ p ◁ (q ◁ r) where
  hom := subst.associator.hom p q r
  inv := subst.associator.inv p q r

set_option linter.dupNamespace false in
/-- Monoidal category structure on Poly via substitution -/
instance Polynomial.subst.monoidalStruct : MonoidalCategoryStruct Poly where
  tensorObj := subst
  whiskerLeft := subst.whiskerLeft
  whiskerRight := @subst.whiskerRight
  tensorUnit := y
  leftUnitor := subst.leftUnitor
  rightUnitor := subst.rightUnitor
  associator := subst.associator

set_option linter.dupNamespace false in
/-- Poly with substitution product is a monoidal category -/
instance Polynomial.subst.monoidal : MonoidalCategory Poly where
  tensorHom_def := by intros; rfl
  id_tensorHom_id := by intros; rfl
  tensorHom_comp_tensorHom := by intros; rfl
  whiskerLeft_id := by intros; rfl
  id_whiskerRight := by intros; rfl
  associator_naturality := by intros; rfl
  leftUnitor_naturality := by intros; rfl
  rightUnitor_naturality := by intros; rfl
  pentagon := by intros; rfl
  triangle := by intros; rfl

end Polynomial

end CategoryTheory
