/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import Mathlib.CategoryTheory.Grothendieck
import HeytingLean.CategoryTheory.Fibred.CoCartesianLift
import HeytingLean.CategoryTheory.Fibred.Fibration

/-!
# Grothendieck Construction is a Cloven Opfibration

The Grothendieck construction of a functor F : C ⥤ Cat produces a **cloven opfibration**
(not a fibration). This is because morphisms in the Grothendieck category have fiber
components of the form `(F.map f).obj X.fiber ⟶ Y.fiber`, which is covariant (pushforward).

For a fibration, one would need F : Cᵒᵖ ⥤ Cat instead.

## Status: WIP QUARANTINE (updated 2026-02-15)

Fiber uniqueness in `cocartesianLiftIsCoCartesian` is now discharged.
The key normalization step is:
- rewrite both sides with `Grothendieck.congr`,
- then use `eqToHom_comp_iff` twice to align the transport shape.

## Main Definitions

* `Grothendieck.forget F`: The projection functor from the Grothendieck construction to C

## Main Results

* `instCoClovenFibrationGrothendieck`: The projection from the Grothendieck
  construction is a cloven opfibration.

## Mathematical Background

According to standard category theory:
- F : C ⥤ Cat → Opfibration (cocartesian lifts)
- F : Cᵒᵖ ⥤ Cat → Fibration (cartesian lifts)

## Implementation Notes

The proof involves careful handling of `eqToHom` coherence when the fiber over `c`
is `x.obj.fiber : F.obj x.obj.base` but `x.obj.base = c` only propositionally.
This creates type coherence challenges that require careful `eqToHom` management.

The key technique from Mathlib's Grothendieck.lean:
- Use `attribute [local simp] eqToHom_map` for fiber coherence
- Use `dsimp` followed by `simp` with eqToHom lemmas

## References

* LeanFibredCategories by Sina Hazratpour
* Mathlib.CategoryTheory.Grothendieck
* Mathlib.CategoryTheory.FiberedCategory.Grothendieck (uses Cᵒᵖ approach)
* nLab: Grothendieck construction
* nLab: Grothendieck fibration
-/

namespace HeytingLean.CategoryTheory.Fibred

open _root_.CategoryTheory
open _root_.CategoryTheory.Category
open BasedLift CoCartesian

universe u v w

variable {C : Type u} [Category.{v} C]

namespace GrothendieckOpfibration

variable (F : C ⥤ Cat.{w, w})

open scoped HeytingLeanFibred

/-- The cocartesian lift target for the Grothendieck construction.

Given f : c ⟶ d and x over c, the target is (d, (F.map f).obj x.fiber).

Note: Since x.obj.base = c (by x.over) but not necessarily definitionally,
we compose eqToHom hx with f to get a morphism from x.obj.base to d. -/
def cocartesianLiftTarget {c d : C} (f : c ⟶ d) (x : (Grothendieck.forget F)⁻¹ c) :
    (Grothendieck.forget F)⁻¹ d := by
  have hx : x.obj.base = c := x.over
  let pushed_fiber : F.obj d := (F.map (eqToHom hx ≫ f)).obj x.obj.fiber
  exact ⟨⟨d, pushed_fiber⟩, rfl⟩

/-- The based lift for the cocartesian lift.

This constructs the canonical morphism from x to the pushforward target,
with base component `eqToHom hx ≫ f` and fiber component the identity
(up to coherence). -/
def cocartesianLiftHom {c d : C} (f : c ⟶ d) (x : (Grothendieck.forget F)⁻¹ c) :
    x ⟶[f] (cocartesianLiftTarget F f x) := by
  have hx : x.obj.base = c := x.over
  let lift_base : x.obj.base ⟶ d := eqToHom hx ≫ f
  let tgt := cocartesianLiftTarget F f x
  -- The fiber is essentially the identity, but requires coherence
  let lift_fiber : (F.map lift_base).obj x.obj.fiber ⟶ tgt.obj.fiber :=
    -- tgt.obj.fiber = (F.map (eqToHom hx ≫ f)).obj x.obj.fiber by definition
    -- lift_base = eqToHom hx ≫ f
    -- So they're definitionally equal
    𝟙 _
  exact ⟨⟨lift_base, lift_fiber⟩, by simp [Grothendieck.forget, lift_base]⟩

-- Enable eqToHom_map for the proof (like Mathlib does in Grothendieck.lean)
-- This must be outside the instance definition
section CoCartesianProof

attribute [local simp] eqToHom_map

/-- The cocartesian lift is cocartesian.

This is the key theorem: given any g' : x ⟶[f ≫ u] z, there exists a unique
factorization through the cocartesian lift.

Proof technique follows Mathlib's Grothendieck.lean:
- Use `attribute [local simp] eqToHom_map` for fiber coherence
- Use `dsimp` followed by `simp` with eqToHom lemmas -/
instance cocartesianLiftIsCoCartesian {c d : C} (f : c ⟶ d) (x : (Grothendieck.forget F)⁻¹ c) :
    CoCartesian (cocartesianLiftHom F f x) where
  uniq_lift := fun {d'} {z} u g' => by
    have hx : x.obj.base = c := x.over
    have hz : z.obj.base = d' := z.over
    let tgt := cocartesianLiftTarget F f x
    have hy : tgt.obj.base = d := rfl

    -- Construct the factorization l : tgt ⟶[u] z
    -- Since hy = rfl, eqToHom hy = 𝟙 d
    let l_base : tgt.obj.base ⟶ z.obj.base := u ≫ eqToHom hz.symm

    -- Key insight: from over_base, g'.hom.base = eqToHom hx ≫ (f ≫ u) ≫ eqToHom hz.symm
    have g'_base_eq : g'.hom.base = eqToHom hx ≫ (f ≫ u) ≫ eqToHom hz.symm := by
      have := over_base g'
      simp only [Grothendieck.forget_map] at this
      exact this

    -- Fiber coherence: (F.map l_base).obj tgt.obj.fiber = (F.map g'.hom.base).obj x.obj.fiber
    have tgt_fiber_eq : tgt.obj.fiber = (F.map (eqToHom hx ≫ f)).obj x.obj.fiber := rfl

    have fiber_type_eq : (F.map l_base).obj tgt.obj.fiber = (F.map g'.hom.base).obj x.obj.fiber := by
      rw [tgt_fiber_eq, g'_base_eq]
      -- Need to show: (F.map l_base).obj ((F.map (eqToHom hx ≫ f)).obj x.obj.fiber)
      --             = (F.map (eqToHom hx ≫ (f ≫ u) ≫ eqToHom hz.symm)).obj x.obj.fiber
      -- Use functoriality: F.map a ⋙ F.map b = F.map (a ≫ b)
      have eq1 : (F.map l_base).obj ((F.map (eqToHom hx ≫ f)).obj x.obj.fiber) =
                 (F.map (eqToHom hx ≫ f) ⋙ F.map l_base).obj x.obj.fiber := rfl
      have eq2 : F.map (eqToHom hx ≫ f) ⋙ F.map l_base = F.map ((eqToHom hx ≫ f) ≫ l_base) :=
        (F.map_comp _ _).symm
      rw [eq1, eq2]
      congr 2
      -- Show: (eqToHom hx ≫ f) ≫ l_base = eqToHom hx ≫ (f ≫ u) ≫ eqToHom hz.symm
      simp only [l_base, Category.assoc]

    let l_fiber : (F.map l_base).obj tgt.obj.fiber ⟶ z.obj.fiber :=
      eqToHom fiber_type_eq ≫ g'.hom.fiber

    let l : tgt.obj ⟶ z.obj := ⟨l_base, l_fiber⟩

    -- The based lift: l lies over u
    -- BasedLift.over requires: P.map hom ≫ eqToHom y.over = eqToHom x.over ≫ f
    -- i.e., l_base ≫ eqToHom hz = eqToHom hy ≫ u
    -- l_base = u ≫ eqToHom hz.symm, hy = rfl
    -- So: (u ≫ eqToHom hz.symm) ≫ eqToHom hz = 𝟙 ≫ u
    --     u ≫ (eqToHom hz.symm ≫ eqToHom hz) = u
    --     u ≫ 𝟙 = u ✓
    have l_over : (Grothendieck.forget F).map l ≫ eqToHom hz = eqToHom hy ≫ u := by
      simp only [Grothendieck.forget_map, l, l_base, eqToHom_refl, Category.id_comp,
                 Category.assoc, eqToHom_trans, Category.comp_id]

    let lLift : tgt ⟶[u] z := ⟨l, l_over⟩
    have hfac_l : (cocartesianLiftHom F f x ≫[l] lLift).hom = g'.hom := by
      -- Grothendieck.ext takes (w_base : f.base = g.base) first, then
      -- (w_fiber : eqToHom _ ≫ f.fiber = g.fiber)
      refine Grothendieck.ext _ _ ?w_base ?w_fiber
      case w_base =>
        simp only [comp_hom, Grothendieck.comp_base]
        dsimp only [cocartesianLiftHom, lLift, l, l_base]
        rw [g'_base_eq]
        simp only [Category.assoc]
      case w_fiber =>
        -- First expand the Grothendieck composition using comp_fiber
        simp only [comp_hom, Grothendieck.comp_fiber]
        -- Unfold the definitions
        dsimp only [cocartesianLiftHom, cocartesianLiftTarget, lLift, l, l_fiber]
        -- The cocartesian lift has fiber = 𝟙, so (F.map l_base).map (𝟙 _) = 𝟙
        simp only [Functor.map_id, Category.id_comp]
        -- Now: eqToHom _ ≫ eqToHom _ ≫ (eqToHom fiber_type_eq ≫ g'.hom.fiber) = g'.hom.fiber
        simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

    use lLift
    constructor
    · exact hfac_l
    · -- Uniqueness: any l' with the same composition equals our chosen lift
      intro l' hl'
      apply BasedLift.ext

      -- First establish base equality
      have base_eq : l'.hom.base = l_base := by
        have hl'_over := over_base l'
        simp only [Grothendieck.forget_map, eqToHom_refl, Category.id_comp] at hl'_over
        exact hl'_over

      refine Grothendieck.ext _ _ ?w_base' ?w_fiber'
      case w_base' =>
        simpa [lLift, l, l_base] using base_eq
      case w_fiber' =>
        have hsame :
            (cocartesianLiftHom F f x ≫[l] l').hom =
              (cocartesianLiftHom F f x ≫[l] lLift).hom := by
          exact hl'.trans hfac_l.symm
        have hcongr := Grothendieck.congr hsame
        simp only [comp_hom, Grothendieck.comp_fiber] at hcongr
        dsimp only [cocartesianLiftHom, cocartesianLiftTarget, lLift, l, l_fiber] at hcongr ⊢
        simp only [Functor.map_id, Category.id_comp] at hcongr
        rw [eqToHom_comp_iff]
        rw [eqToHom_comp_iff] at hcongr
        simpa [Category.assoc, eqToHom_trans] using hcongr

end CoCartesianProof

/-- The projection functor of a Grothendieck construction is a cloven opfibration. -/
instance instCoClovenFibrationGrothendieck : CoClovenFibration (Grothendieck.forget F) where
  tgt f x := cocartesianLiftTarget F f x
  colift f x := cocartesianLiftHom F f x
  is_cocart f x := fun {_d'} {_z} u g' => (cocartesianLiftIsCoCartesian F f x).uniq_lift u g'

/-- Main result: The Grothendieck construction projection is a cloven opfibration.
    This is provided as the instance `instCoClovenFibrationGrothendieck` above. -/
example : CoClovenFibration (Grothendieck.forget F) := inferInstance

end GrothendieckOpfibration

end HeytingLean.CategoryTheory.Fibred
