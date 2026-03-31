/-
Copyright (c) 2023 David Spivak, Shaowei Lin. All rights reserved.
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Polynomial Functors - Tensor Product
====================================

The tensor (parallel) product makes Poly a symmetric monoidal closed category.

## Main Definitions

* `tensor` - Tensor product p ⊗ q
* `homTensor` - Internal hom ⟦p, q⟧
* Symmetric monoidal closed structure

## References

* [Polynomial Functors Book](https://toposinstitute.github.io/poly/poly-book.pdf)
-/

import HeytingLean.CategoryTheory.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Closed.Monoidal

namespace CategoryTheory

namespace Polynomial

open Polynomial

/-!
## Tensor (Parallel) Product
-/

/-- Tensor/parallel product of polynomial functors -/
def tensor (p q : Poly.{u, u}) : Poly.{u, u} where
  pos := p.pos × q.pos
  dir := fun (ppos, qpos) => (p.dir ppos) × (q.dir qpos)

/-- Notation for tensor product -/
scoped infixr:90 " ⊗ᵖ " => tensor

/-- Bifunctorial action of tensor on morphisms -/
def tensor.map {p q r z : Poly.{u, u}} (f : p ⟶ q) (g : r ⟶ z) :
    (p ⊗ᵖ r) ⟶ (q ⊗ᵖ z) where
  onPos := fun (ppos, rpos) => (f.onPos ppos, g.onPos rpos)
  onDir := fun (ppos, rpos) (qdir, zdir) =>
    (f.onDir ppos qdir, g.onDir rpos zdir)

/-- Whisker tensor on the left -/
def tensor.whiskerLeft (p : Poly) {q q' : Poly} (f : q ⟶ q') :
    (p ⊗ᵖ q) ⟶ (p ⊗ᵖ q') :=
  tensor.map (𝟙 p) f

/-- Whisker tensor on the right -/
def tensor.whiskerRight {p p' : Poly} (f : p ⟶ p') (q : Poly) :
    (p ⊗ᵖ q) ⟶ (p' ⊗ᵖ q) :=
  tensor.map f (𝟙 q)

/-- First projection after tensor -/
def tensor.first {p q r : Poly.{u, u}} (f : p ⟶ r) : (p ⊗ᵖ q) ⟶ (r ⊗ᵖ q) :=
  tensor.map f (𝟙 q)

/-- Second projection after tensor -/
def tensor.second {p q r : Poly.{u, u}} (g : q ⟶ r) : (p ⊗ᵖ q) ⟶ (p ⊗ᵖ r) :=
  tensor.map (𝟙 p) g

/-- Symmetry/swap for tensor -/
def tensor.swap {p q : Poly} : (p ⊗ᵖ q) ⟶ (q ⊗ᵖ p) where
  onPos := fun (ppos, qpos) => (qpos, ppos)
  onDir := fun _ (qdir, pdir) => (pdir, qdir)

/-- Associator forward direction -/
def tensor.assoc.fwd {p q r : Poly} : (p ⊗ᵖ (q ⊗ᵖ r)) ⟶ ((p ⊗ᵖ q) ⊗ᵖ r) where
  onPos := fun (ppos, qpos, rpos) => ((ppos, qpos), rpos)
  onDir := fun _ ((pdir, qdir), rdir) => (pdir, qdir, rdir)

/-- Associator backward direction -/
def tensor.assoc.bwd {p q r : Poly} : ((p ⊗ᵖ q) ⊗ᵖ r) ⟶ (p ⊗ᵖ (q ⊗ᵖ r)) where
  onPos := fun ((ppos, qpos), rpos) => (ppos, qpos, rpos)
  onDir := fun _ (pdir, qdir, rdir) => ((pdir, qdir), rdir)

/-- Split left: duplicate positions, project left direction -/
def tensor.split.l {p : Poly} : p ⟶ (p ⊗ᵖ p) where
  onPos := fun ppos => (ppos, ppos)
  onDir := fun _ (f, _) => f

/-- Split right: duplicate positions, project right direction -/
def tensor.split.r {p : Poly} : p ⟶ (p ⊗ᵖ p) where
  onPos := fun ppos => (ppos, ppos)
  onDir := fun _ (_, g) => g

/-- Left unit forward -/
def tensor.unit.l.fwd {p : Poly} : (y ⊗ᵖ p) ⟶ p where
  onPos := fun (_, ppos) => ppos
  onDir := fun (u, _) pdir => (u, pdir)

/-- Left unit backward -/
def tensor.unit.l.bwd {p : Poly} : p ⟶ (y ⊗ᵖ p) where
  onPos := fun ppos => (PUnit.unit, ppos)
  onDir := fun _ (_, pdir) => pdir

/-- Right unit forward -/
def tensor.unit.r.fwd {p : Poly} : (p ⊗ᵖ y) ⟶ p where
  onPos := fun (ppos, _) => ppos
  onDir := fun (_, u) pdir => (pdir, u)

/-- Right unit backward -/
def tensor.unit.r.bwd {p : Poly} : p ⟶ (p ⊗ᵖ y) where
  onPos := fun ppos => (ppos, PUnit.unit)
  onDir := fun _ (pdir, _) => pdir

/-- Left unitor isomorphism for tensor -/
def tensor.leftUnitor (p : Poly) : (y ⊗ᵖ p) ≅ p where
  hom := tensor.unit.l.fwd
  inv := tensor.unit.l.bwd

/-- Right unitor isomorphism for tensor -/
def tensor.rightUnitor (p : Poly) : (p ⊗ᵖ y) ≅ p where
  hom := tensor.unit.r.fwd
  inv := tensor.unit.r.bwd

/-- Associator isomorphism for tensor -/
def tensor.associator (p q r : Poly) : ((p ⊗ᵖ q) ⊗ᵖ r) ≅ (p ⊗ᵖ (q ⊗ᵖ r)) where
  hom := tensor.assoc.bwd
  inv := tensor.assoc.fwd

/-!
## Internal Hom (Closure)
-/

/-- The internal hom object for tensor product -/
def homTensor (q r : Poly.{u, u}) : Poly.{u, u} where
  pos := q ⟶ r
  dir := fun φ => Σ (j : q.pos), (r.dir (φ.onPos j))

/-- Notation for internal hom: ⦃p, q⦄ -/
scoped notation:95 "⦃" A:80 "," B:80 "⦄" => homTensor A B

/-- Functorial action of internal hom on the second argument -/
def homTensor.closed.right.fmap {p q r : Poly} (f : q ⟶ r) :
    (⦃p, q⦄ ⟶ ⦃p, r⦄) where
  onPos := (· ≫ f)
  onDir := fun _ ⟨pPos, toDirR⟩ => ⟨pPos, f.onDir _ toDirR⟩

/-- The functor ⦃r, -⦄ -/
def homTensor.closed.right (r : Poly) : Poly ⥤ Poly where
  obj := fun x => ⦃r, x⦄
  map := fun f => homTensor.closed.right.fmap f

/-- Evaluation morphism: ⦃p, r⦄ ⊗ᵖ p ⟶ r -/
def homTensor.eval (p r : Poly) : (⦃p, r⦄ ⊗ᵖ p) ⟶ r where
  onPos := fun (φ, pPos) => φ.onPos pPos
  onDir := fun (φ, pPos) dirR => (⟨pPos, dirR⟩, φ.onDir pPos dirR)

/-- Currying: (p ⊗ᵖ X ⟶ Y) → (X ⟶ ⦃p, Y⦄) -/
def homTensor.closed.adjunction.homEquiv.toFun {p X Y : Poly}
    (φ : (p ⊗ᵖ X) ⟶ Y) : (X ⟶ ⦃p, Y⦄) where
  onPos := fun xPos => {
    onPos := fun pPos => φ.onPos (pPos, xPos)
    onDir := fun pPos yDir =>
      let ⟨dirp, _⟩ := φ.onDir (pPos, xPos) yDir
      dirp
  }
  onDir := fun xPos homDir =>
    match homDir with
    | ⟨pPos, ydir⟩ =>
      let ⟨_, dirx⟩ := φ.onDir (pPos, xPos) ydir
      dirx

/-- Uncurrying: (X ⟶ ⦃p, Y⦄) → (p ⊗ᵖ X ⟶ Y) -/
def homTensor.closed.adjunction.homEquiv.invFun {p X Y : Poly}
    (ψ : X ⟶ ⦃p, Y⦄) : (p ⊗ᵖ X) ⟶ Y where
  onPos := fun (pPos, xPos) =>
    let intermediate := ψ.onPos xPos
    intermediate.onPos pPos
  onDir := fun (pPos, xPos) pyDir =>
    let intermediate := ψ.onPos xPos
    (intermediate.onDir pPos pyDir, ψ.onDir xPos ⟨pPos, pyDir⟩)

/-- The curry-uncurry equivalence -/
def homTensor.closed.adjunction.homEquiv (p X Y : Poly) :
    ((p ⊗ᵖ X) ⟶ Y) ≃ (X ⟶ ⦃p, Y⦄) where
  toFun := homTensor.closed.adjunction.homEquiv.toFun
  invFun := homTensor.closed.adjunction.homEquiv.invFun
  left_inv := by
    intro ψ
    simp only [homTensor.closed.adjunction.homEquiv.toFun,
               homTensor.closed.adjunction.homEquiv.invFun]
    rfl
  right_inv := by
    intro ψ
    simp only [homTensor.closed.adjunction.homEquiv.toFun,
               homTensor.closed.adjunction.homEquiv.invFun]
    rfl

end Polynomial

end CategoryTheory
