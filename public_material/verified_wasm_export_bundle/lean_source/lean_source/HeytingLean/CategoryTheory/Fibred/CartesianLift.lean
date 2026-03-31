/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original work: Sina Hazratpour (LeanFibredCategories)
Port: HeytingLean
-/

import HeytingLean.CategoryTheory.Fibred.Basic

/-!
# Cartesian Lifts

A based lift g : x ⟶[f] y is cartesian if it satisfies the universal property:
for any other lift g' : z ⟶[u ≫ f] y, there is a unique factorization through g.

## Main Definitions

* `Cartesian`: Predicate that a based lift is cartesian
* `gaplift`: The universal gap lift
* `CartLift`: A cartesian lift structure (src + based_lift + cartesian proof)

## Main Results

* `gaplift_property`: Composition of gaplift with cartesian lift gives the original
* `gaplift_uniq`: Uniqueness of the gap lift
* `cart_comp`: Cartesian lifts are closed under composition

## References

* LeanFibredCategories by Sina Hazratpour
* nLab: Cartesian morphism
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

/-- A based lift g : x ⟶[f] y is cartesian if for every u : c' ⟶ c and
    every lift g' : z ⟶[u ≫ f] y, there exists a unique l : z ⟶[u] x
    such that l ≫[l] g = g'. -/
class Cartesian {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : x ⟶[f] y) : Prop where
  /-- Universal property: unique factorization -/
  uniq_lift : ∀ {c' : C} {z : P⁻¹ c'} (u : c' ⟶ c) (g' : z ⟶[u ≫ f] y),
    ∃! (l : z ⟶[u] x), (l ≫[l] g).hom = g'.hom

namespace Cartesian

variable {c d c' : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d}
variable (g : x ⟶[f] y) [hg : Cartesian g]

/-- The gap lift: the unique morphism factoring through the cartesian lift -/
noncomputable def gaplift {z : P⁻¹ c'} (u : c' ⟶ c) (g' : z ⟶[u ≫ f] y) : z ⟶[u] x :=
  Classical.choose (hg.uniq_lift u g')

/-- The gap lift composes with g to give g' -/
@[simp]
lemma gaplift_property {z : P⁻¹ c'} (u : c' ⟶ c) (g' : z ⟶[u ≫ f] y) :
    (gaplift g u g' ≫[l] g).hom = g'.hom :=
  (Classical.choose_spec (hg.uniq_lift u g')).1

/-- The gap lift composed with g equals g' as based lifts -/
lemma gaplift_comp_eq {z : P⁻¹ c'} (u : c' ⟶ c) (g' : z ⟶[u ≫ f] y) :
    gaplift g u g' ≫[l] g = g' := by
  ext; exact gaplift_property g u g'

/-- Uniqueness of gap lift: any other factorization equals gaplift -/
@[simp]
lemma gaplift_uniq {z : P⁻¹ c'} {u : c' ⟶ c} (g' : z ⟶[u ≫ f] y)
    (l : z ⟶[u] x) (hl : (l ≫[l] g).hom = g'.hom) : l = gaplift g u g' := by
  have h := (Classical.choose_spec (hg.uniq_lift u g')).2
  exact h l hl

/-- Variant: two lifts that compose the same way are equal -/
lemma gaplift_uniq' {z : P⁻¹ c'} {u : c' ⟶ c}
    (l₁ l₂ : z ⟶[u] x) (h : (l₁ ≫[l] g).hom = (l₂ ≫[l] g).hom) : l₁ = l₂ := by
  have h1 := gaplift_uniq g (l₂ ≫[l] g) l₁ h
  have h2 := gaplift_uniq g (l₂ ≫[l] g) l₂ rfl
  exact h1.trans h2.symm

end Cartesian

/-- A cartesian lift structure: source, based lift, and proof of cartesianness -/
structure CartLift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) where
  /-- The source of the lift -/
  src : P⁻¹ c
  /-- The based lift from src to y over f -/
  based_lift : src ⟶[f] y
  /-- The lift is cartesian -/
  is_cart : Cartesian based_lift

/-- Existence of a cartesian lift -/
def HasCartLift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : Prop :=
  Nonempty (CartLift (P := P) f y)

/-- Cartesian lifts are closed under composition -/
instance cart_comp {c d e : C} {f : c ⟶ d} {g : d ⟶ e}
    {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ e}
    (l₁ : x ⟶[f] y) [Cartesian l₁]
    (l₂ : y ⟶[g] z) [Cartesian l₂] : Cartesian (l₁ ≫[l] l₂) where
  uniq_lift := fun {c'} {w} u g' => by
    -- First factor through l₂
    let g₂' := g' |>.cast (assoc u f g).symm
    let k₂ := Cartesian.gaplift l₂ (u ≫ f) g₂'
    -- Then factor through l₁
    let k₁ := Cartesian.gaplift l₁ u k₂
    use k₁
    constructor
    · -- Need to show: (k₁ ≫[l] l₁ ≫[l] l₂).hom = g'.hom
      -- By gaplift_property for l₁: (k₁ ≫[l] l₁).hom = k₂.hom
      -- By gaplift_property for l₂: (k₂ ≫[l] l₂).hom = g₂'.hom = g'.hom
      have hk1 : (k₁ ≫[l] l₁).hom = k₂.hom := Cartesian.gaplift_property l₁ u k₂
      have hk2 : (k₂ ≫[l] l₂).hom = g₂'.hom := Cartesian.gaplift_property l₂ (u ≫ f) g₂'
      simp only [comp_hom] at hk1 hk2 ⊢
      calc k₁.hom ≫ l₁.hom ≫ l₂.hom
          = (k₁.hom ≫ l₁.hom) ≫ l₂.hom := by rw [Category.assoc]
        _ = k₂.hom ≫ l₂.hom := by rw [hk1]
        _ = g₂'.hom := hk2
        _ = g'.hom := rfl
    · intro l hl
      -- Show l = k₁ by uniqueness
      have h₁ : (l ≫[l] l₁ ≫[l] l₂).hom = g'.hom := hl
      -- First show l ≫[l] l₁ = k₂
      have h₂ : l ≫[l] l₁ = k₂ := by
        apply Cartesian.gaplift_uniq' l₂
        simp only [comp_hom] at h₁ ⊢
        have hk2 : (k₂ ≫[l] l₂).hom = g₂'.hom := Cartesian.gaplift_property l₂ (u ≫ f) g₂'
        simp only [comp_hom] at hk2
        calc (l.hom ≫ l₁.hom) ≫ l₂.hom
            = l.hom ≫ l₁.hom ≫ l₂.hom := by rw [Category.assoc]
          _ = g'.hom := h₁
          _ = g₂'.hom := rfl
          _ = k₂.hom ≫ l₂.hom := hk2.symm
      -- Then show l = k₁
      apply Cartesian.gaplift_uniq l₁
      have h₂' : (l ≫[l] l₁).hom = k₂.hom := congrArg BasedLift.hom h₂
      simp only [comp_hom] at h₂' ⊢
      exact h₂'

/-- Identity based lift is cartesian -/
instance cart_id (x : P⁻¹ c) : Cartesian (BasedLift.id (P := P) x) where
  uniq_lift := fun {c'} {z} u g' => by
    use g' |>.cast (comp_id u)
    constructor
    · simp
    · intro l hl; ext; simp at hl ⊢; exact hl

/-- Isomorphisms are cartesian -/
instance cart_iso {x y : E} (g : x ⟶ y) [IsIso g] :
    Cartesian (BasedLift.tauto (P := P) g) where
  uniq_lift := fun {c'} {z} u g' => by
    use ⟨g'.hom ≫ inv g, by simp [BasedLift.over_base g']⟩
    constructor
    · simp
    · intro l hl; ext
      simp only [BasedLift.tauto, Fiber.tauto] at hl
      simp [← hl]

end HeytingLean.CategoryTheory.Fibred
