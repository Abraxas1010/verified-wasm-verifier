/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original work: Sina Hazratpour (LeanFibredCategories)
Port: HeytingLean
-/

import HeytingLean.CategoryTheory.Fibred.Basic

/-!
# Cocartesian Lifts

A based lift g : x ⟶[f] y is cocartesian if it satisfies the universal property:
for any other lift g' : x ⟶[f ≫ u] z, there is a unique factorization through g.

This is the dual of cartesian lifts. Cocartesian lifts appear in opfibrations,
and the Grothendieck construction of F : C ⥤ Cat produces cocartesian lifts.

## Main Definitions

* `CoCartesian`: Predicate that a based lift is cocartesian
* `cogaplift`: The universal gap lift
* `CoCartLift`: A cocartesian lift structure (tgt + based_lift + cocartesian proof)

## Main Results

* `cogaplift_property`: Composition of cocartesian lift with cogaplift gives the original
* `cogaplift_uniq`: Uniqueness of the gap lift
* `cocart_comp`: Cocartesian lifts are closed under composition

## References

* LeanFibredCategories by Sina Hazratpour
* nLab: Cocartesian morphism
-/

namespace HeytingLean.CategoryTheory.Fibred

open _root_.CategoryTheory
open _root_.CategoryTheory.Category
open BasedLift

universe u v w

variable {C : Type u} [Category.{v} C]
variable {E : Type w} [Category E]
variable {P : E ⥤ C}

open scoped HeytingLeanFibred

/-- A based lift g : x ⟶[f] y is cocartesian if for every u : d ⟶ d' and
    every lift g' : x ⟶[f ≫ u] z, there exists a unique l : y ⟶[u] z
    such that g ≫[l] l = g'. -/
class CoCartesian {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : x ⟶[f] y) : Prop where
  /-- Universal property: unique factorization -/
  uniq_lift : ∀ {d' : C} {z : P⁻¹ d'} (u : d ⟶ d') (g' : x ⟶[f ≫ u] z),
    ∃! (l : y ⟶[u] z), (g ≫[l] l).hom = g'.hom

namespace CoCartesian

variable {c d d' : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d}
variable (g : x ⟶[f] y) [hg : CoCartesian g]

/-- The cogap lift: the unique morphism factoring through the cocartesian lift -/
noncomputable def cogaplift {z : P⁻¹ d'} (u : d ⟶ d') (g' : x ⟶[f ≫ u] z) : y ⟶[u] z :=
  Classical.choose (hg.uniq_lift u g')

/-- The cogap lift composes with g to give g' -/
@[simp]
lemma cogaplift_property {z : P⁻¹ d'} (u : d ⟶ d') (g' : x ⟶[f ≫ u] z) :
    (g ≫[l] cogaplift g u g').hom = g'.hom :=
  (Classical.choose_spec (hg.uniq_lift u g')).1

/-- The cocartesian lift composed with cogaplift equals g' as based lifts -/
lemma cogaplift_comp_eq {z : P⁻¹ d'} (u : d ⟶ d') (g' : x ⟶[f ≫ u] z) :
    g ≫[l] cogaplift g u g' = g' := by
  ext; exact cogaplift_property g u g'

/-- Uniqueness of cogap lift: any other factorization equals cogaplift -/
@[simp]
lemma cogaplift_uniq {z : P⁻¹ d'} {u : d ⟶ d'} (g' : x ⟶[f ≫ u] z)
    (l : y ⟶[u] z) (hl : (g ≫[l] l).hom = g'.hom) : l = cogaplift g u g' := by
  have h := (Classical.choose_spec (hg.uniq_lift u g')).2
  exact h l hl

/-- Variant: two lifts that compose the same way are equal -/
lemma cogaplift_uniq' {z : P⁻¹ d'} {u : d ⟶ d'}
    (l₁ l₂ : y ⟶[u] z) (h : (g ≫[l] l₁).hom = (g ≫[l] l₂).hom) : l₁ = l₂ := by
  have h1 := cogaplift_uniq g (g ≫[l] l₂) l₁ h
  have h2 := cogaplift_uniq g (g ≫[l] l₂) l₂ rfl
  exact h1.trans h2.symm

end CoCartesian

/-- A cocartesian lift structure: target, based lift, and proof of cocartesianness -/
structure CoCartLift {c d : C} (f : c ⟶ d) (x : P⁻¹ c) where
  /-- The target of the lift -/
  tgt : P⁻¹ d
  /-- The based lift from x to tgt over f -/
  based_lift : x ⟶[f] tgt
  /-- The lift is cocartesian -/
  is_cocart : CoCartesian based_lift

/-- Existence of a cocartesian lift -/
def HasCoCartLift {c d : C} (f : c ⟶ d) (x : P⁻¹ c) : Prop :=
  Nonempty (CoCartLift (P := P) f x)

/-- Cocartesian lifts are closed under composition -/
instance cocart_comp {c d e : C} {f : c ⟶ d} {g : d ⟶ e}
    {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ e}
    (l₁ : x ⟶[f] y) [CoCartesian l₁]
    (l₂ : y ⟶[g] z) [CoCartesian l₂] : CoCartesian (l₁ ≫[l] l₂) where
  uniq_lift := fun {e'} {w} u g' => by
    -- First factor through l₁ to get a lift over g ≫ u
    let g₁' := g' |>.cast (assoc f g u)
    let k₁ := CoCartesian.cogaplift l₁ (g ≫ u) g₁'
    -- Then factor through l₂
    let k₂ := CoCartesian.cogaplift l₂ u k₁
    use k₂
    constructor
    · -- Need to show: ((l₁ ≫[l] l₂) ≫[l] k₂).hom = g'.hom
      have hk2 : (l₂ ≫[l] k₂).hom = k₁.hom := CoCartesian.cogaplift_property l₂ u k₁
      have hk1 : (l₁ ≫[l] k₁).hom = g₁'.hom := CoCartesian.cogaplift_property l₁ (g ≫ u) g₁'
      simp only [comp_hom] at hk1 hk2 ⊢
      calc (l₁.hom ≫ l₂.hom) ≫ k₂.hom
          = l₁.hom ≫ (l₂.hom ≫ k₂.hom) := by rw [Category.assoc]
        _ = l₁.hom ≫ k₁.hom := by rw [hk2]
        _ = g₁'.hom := hk1
        _ = g'.hom := rfl
    · intro l hl
      -- Show l = k₂ by uniqueness
      have h₁ : ((l₁ ≫[l] l₂) ≫[l] l).hom = g'.hom := hl
      -- First show l₂ ≫[l] l = k₁
      have h₂ : l₂ ≫[l] l = k₁ := by
        apply CoCartesian.cogaplift_uniq' l₁
        simp only [comp_hom] at h₁ ⊢
        have hk1 : (l₁ ≫[l] k₁).hom = g₁'.hom := CoCartesian.cogaplift_property l₁ (g ≫ u) g₁'
        simp only [comp_hom] at hk1
        calc l₁.hom ≫ (l₂.hom ≫ l.hom)
            = l₁.hom ≫ l₂.hom ≫ l.hom := rfl
          _ = (l₁.hom ≫ l₂.hom) ≫ l.hom := by rw [← Category.assoc]
          _ = g'.hom := h₁
          _ = g₁'.hom := rfl
          _ = l₁.hom ≫ k₁.hom := hk1.symm
      -- Then show l = k₂
      apply CoCartesian.cogaplift_uniq l₂
      have h₂' : (l₂ ≫[l] l).hom = k₁.hom := congrArg BasedLift.hom h₂
      simp only [comp_hom] at h₂' ⊢
      exact h₂'

/-- Identity based lift is cocartesian -/
instance cocart_id (x : P⁻¹ c) : CoCartesian (BasedLift.id (P := P) x) where
  uniq_lift := fun {d'} {z} u g' => by
    use g' |>.cast (id_comp u)
    constructor
    · simp
    · intro l hl; ext; simp at hl ⊢; exact hl

/-- Isomorphisms are cocartesian -/
instance cocart_iso {x y : E} (g : x ⟶ y) [IsIso g] :
    CoCartesian (BasedLift.tauto (P := P) g) where
  uniq_lift := fun {d'} {z} u g' => by
    use ⟨inv g ≫ g'.hom, by simp [BasedLift.over_base g']⟩
    constructor
    · simp
    · intro l hl; ext
      simp only [BasedLift.tauto, Fiber.tauto] at hl
      simp [← hl]

end HeytingLean.CategoryTheory.Fibred
