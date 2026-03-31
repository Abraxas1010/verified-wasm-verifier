/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Locally Cartesian Closed Categories - Basic Definitions
========================================================

This module provides the fundamental infrastructure for locally cartesian closed
categories (LCCC), adapted from sinhp/Poly for compatibility with mathlib v4.24.0.

## Main Definitions

* `ExponentiableMorphism f` - A morphism where `Over.pullback f` has a right adjoint
* `pushforward f` - The right adjoint to pullback (dependent product Π_f)
* `pullbackPushforwardAdj f` - The adjunction `pullback f ⊣ pushforward f`

## Mathematical Background

An LCCC has a triple adjunction for each morphism `f : X ⟶ Y`:

```
Over.map f ⊣ Over.pullback f ⊣ pushforward f
```

- `map f` (composition): postcompose with f
- `pullback f` (base change): pull back along f
- `pushforward f` (dependent product): Π_f, the right adjoint to pullback

A category is locally cartesian closed iff every morphism is exponentiable.

## References

* sinhp/Poly - Original Lean 4 formalization (v4.27.0)
* [nLab: Locally cartesian closed category](https://ncatlab.org/nlab/show/locally+cartesian+closed+category)
* Hazratpour & Riehl (2024) - 2-categorical Frobenius for fibrations
-/

import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.MorphismProperty.Basic

namespace HeytingLean.CategoryTheory.LCCC

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Over
open _root_.CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C]

/-! ## Exponentiable Morphisms -/

/-- A morphism `f : X ⟶ Y` is **exponentiable** if the pullback functor
`Over.pullback f : Over Y ⥤ Over X` has a right adjoint.

This right adjoint is called the **pushforward** or **dependent product** `Π_f`.

In a locally cartesian closed category, every morphism is exponentiable. -/
abbrev ExponentiableMorphism [HasPullbacks C] : MorphismProperty C :=
  fun _ _ f ↦ (Over.pullback f).IsLeftAdjoint

namespace ExponentiableMorphism

variable [HasPullbacks C] {X Y : C}

/-- The pushforward (dependent product) functor `Π_f : Over X ⥤ Over Y`.

This is the right adjoint to `Over.pullback f`. -/
noncomputable abbrev pushforward (f : X ⟶ Y) [h : ExponentiableMorphism f] : Over X ⥤ Over Y :=
  (Over.pullback f).rightAdjoint

/-- The adjunction `Over.pullback f ⊣ pushforward f`. -/
noncomputable def adj (f : X ⟶ Y) [ExponentiableMorphism f] :
    Over.pullback f ⊣ pushforward f :=
  Adjunction.ofIsLeftAdjoint (Over.pullback f)

/-- The counit of the pullback-pushforward adjunction (dependent evaluation). -/
noncomputable abbrev ev (f : X ⟶ Y) [ExponentiableMorphism f] :
    pushforward f ⋙ Over.pullback f ⟶ 𝟭 _ :=
  (adj f).counit

/-- The unit of the pullback-pushforward adjunction (dependent coevaluation). -/
noncomputable abbrev coev (f : X ⟶ Y) [ExponentiableMorphism f] :
    𝟭 _ ⟶ Over.pullback f ⋙ pushforward f :=
  (adj f).unit

/-- Currying: turn a morphism in `Over X` into one in `Over Y` via pushforward. -/
noncomputable def pushforwardCurry [ExponentiableMorphism f] {A : Over Y} {B : Over X}
    (u : (Over.pullback f).obj A ⟶ B) : A ⟶ (pushforward f).obj B :=
  (adj f).homEquiv A B u

/-- Uncurrying: turn a morphism in `Over Y` into one in `Over X` via pullback. -/
noncomputable def pushforwardUncurry [ExponentiableMorphism f] {A : Over Y} {B : Over X}
    (v : A ⟶ (pushforward f).obj B) : (Over.pullback f).obj A ⟶ B :=
  ((adj f).homEquiv A B).symm v

@[simp]
theorem pushforward_uncurry_curry [ExponentiableMorphism f] {A : Over Y} {B : Over X}
    (u : (Over.pullback f).obj A ⟶ B) :
    pushforwardUncurry (pushforwardCurry u) = u :=
  ((adj f).homEquiv A B).left_inv u

@[simp]
theorem pushforward_curry_uncurry [ExponentiableMorphism f] {A : Over Y} {B : Over X}
    (v : A ⟶ (pushforward f).obj B) :
    pushforwardCurry (pushforwardUncurry v) = v :=
  ((adj f).homEquiv A B).right_inv v

/-- Identity morphisms are exponentiable. -/
instance id_exponentiable : ExponentiableMorphism (𝟙 X) := by
  -- pullback along id is isomorphic to identity, so it's a left adjoint to itself
  have : Over.pullback (𝟙 X) ≅ 𝟭 (Over X) := Over.pullbackId
  exact ⟨𝟭 (Over X), ⟨Adjunction.id.ofNatIsoLeft this.symm⟩⟩

/-- Composition of exponentiable morphisms is exponentiable.
If f and g are exponentiable, then `f ≫ g` is exponentiable with
pushforward `pushforward f ⋙ pushforward g`. -/
instance comp_exponentiable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    ExponentiableMorphism (f ≫ g) := by
  -- pullback (f ≫ g) ≅ pullback g ⋙ pullback f (by pullbackComp)
  -- So if pullback f ⊣ pushforward f and pullback g ⊣ pushforward g,
  -- then pullback (f ≫ g) ⊣ pushforward f ⋙ pushforward g
  refine ⟨pushforward f ⋙ pushforward g, ⟨?_⟩⟩
  have adj_f := adj f
  have adj_g := adj g
  -- Compose the adjunctions: (pullback g ⋙ pullback f) ⊣ (pushforward f ⋙ pushforward g)
  have comp_adj := adj_g.comp adj_f
  -- Use the iso pullback (f ≫ g) ≅ pullback g ⋙ pullback f
  exact comp_adj.ofNatIsoLeft (Over.pullbackComp f g).symm

/-- Isomorphisms are exponentiable.

When f is an iso, `pullback f` is a left adjoint with right adjoint `pullback (inv f)`.
This follows because:
1. `mapIso (asIso f)` gives an equivalence with inverse `map (inv f)`
2. The equivalence adjunction gives `map f ⊣ map (inv f)`
3. By uniqueness of right adjoints: `pullback f ≅ map (inv f)`
4. So `pullback f` is isomorphic to a left adjoint (via mapPullbackAdj (inv f))
-/
instance iso_exponentiable {f : X ⟶ Y} [IsIso f] : ExponentiableMorphism f := by
  -- The equivalence induced by the isomorphism
  let e : Over X ≌ Over Y := Over.mapIso (asIso f)
  -- e.toAdjunction : map f ⊣ map (inv f)
  -- mapPullbackAdj f : map f ⊣ pullback f
  -- By uniqueness of right adjoints: pullback f ≅ map (inv f)
  have h_iso : Over.pullback f ≅ e.inverse :=
    (Over.mapPullbackAdj f).rightAdjointUniq e.toAdjunction
  -- e.inverse = map (inv f), which is a left adjoint via mapPullbackAdj (inv f)
  -- So pullback f is also a left adjoint (to pullback (inv f))
  have h_inv_adj : Over.map (inv f) ⊣ Over.pullback (inv f) := Over.mapPullbackAdj (inv f)
  -- Construct the adjunction: pullback f ⊣ pullback (inv f)
  exact ⟨Over.pullback (inv f), ⟨h_inv_adj.ofNatIsoLeft h_iso.symm⟩⟩

end ExponentiableMorphism

/-! ## Locally Cartesian Closed Categories -/

/-- A category is **locally cartesian closed** if every morphism is exponentiable.

Equivalently, for every morphism `f`, the pullback functor has a right adjoint. -/
class LocallyCartesianClosed (C : Type u) [Category.{v} C] [HasPullbacks C] : Prop where
  exponentiable : ∀ {X Y : C} (f : X ⟶ Y), ExponentiableMorphism f

namespace LocallyCartesianClosed

variable [HasPullbacks C] [LocallyCartesianClosed C] {X Y : C}

instance (f : X ⟶ Y) : ExponentiableMorphism f := exponentiable f

/-- In an LCCC, we always have the pushforward functor (dependent product). -/
noncomputable abbrev depProd (f : X ⟶ Y) : Over X ⥤ Over Y :=
  ExponentiableMorphism.pushforward f

/-- In an LCCC, we always have the pullback-pushforward adjunction. -/
noncomputable def pullbackPushforwardAdj (f : X ⟶ Y) : Over.pullback f ⊣ depProd f :=
  ExponentiableMorphism.adj f

end LocallyCartesianClosed

/-! ## Connection to Polynomial Functors -/

/-- The polynomial functor associated to an exponentiable morphism.

For `p : E ⟶ B` exponentiable, the polynomial functor `P_p : C ⥤ C` is:
  `X ↦ Σ_{b : B} X^{E_b}`

where `E_b = p⁻¹(b)` is the fiber over `b`.

This is computed as: `star E ⋙ pushforward p ⋙ forget B`. -/
noncomputable def polynomialFunctor [HasPullbacks C] [HasBinaryProducts C]
    {E B : C} (p : E ⟶ B) [ExponentiableMorphism p] : C ⥤ C :=
  Over.star E ⋙ ExponentiableMorphism.pushforward p ⋙ Over.forget B

end HeytingLean.CategoryTheory.LCCC
