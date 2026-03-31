/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original work: Sina Hazratpour (LeanFibredCategories)
Port: HeytingLean
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Grothendieck

/-!
# Fiber Categories and Based Lifts

This module provides the fundamental infrastructure for fibred category theory:
- Fiber categories `P⁻¹ c` for a functor `P : E ⥤ C`
- Based lifts: morphisms in the total category lying over base morphisms
- Composition and identity for based lifts

## Main Definitions

* `Fiber P c`: The fiber of functor `P` over object `c`
* `BasedLift P f x y`: A morphism from `x` to `y` lying over `f`
* `BasedLift.comp`: Composition of based lifts
* `BasedLift.id`: Identity based lift

## References

* LeanFibredCategories by Sina Hazratpour
* nLab: Grothendieck fibration
-/

namespace HeytingLean.CategoryTheory.Fibred

open _root_.CategoryTheory
open _root_.CategoryTheory.Category

universe u v w

variable {C : Type u} [Category.{v} C]
variable {E : Type w} [Category E]

/-- The fiber of a functor P : E ⥤ C over an object c : C.
    Objects are pairs (e, proof that P.obj e = c). -/
structure Fiber (P : E ⥤ C) (c : C) where
  /-- The object in the total category -/
  obj : E
  /-- Proof that it lies over c -/
  over : P.obj obj = c

namespace Fiber

variable {P : E ⥤ C} {c : C}

/-- Coercion from fiber object to total category object -/
instance : CoeOut (Fiber P c) E where
  coe := fun x => x.obj

/-- Create a fiber element from an object with proof -/
@[simp]
def mk' (e : E) (h : P.obj e = c) : Fiber P c := ⟨e, h⟩

/-- The tautological fiber element for an object e over P.obj e -/
@[simp]
def tauto (e : E) : Fiber P (P.obj e) := ⟨e, rfl⟩

@[simp]
lemma tauto_obj (e : E) : (tauto (P := P) e).obj = e := rfl

@[simp]
lemma coe_mk (e : E) (h : P.obj e = c) : ((⟨e, h⟩ : Fiber P c) : E) = e := rfl

end Fiber

/-- Notation for fiber category: P⁻¹ c -/
scoped[HeytingLeanFibred] notation:max P "⁻¹" c =>
  _root_.HeytingLean.CategoryTheory.Fibred.Fiber P c

open scoped HeytingLeanFibred

/-- Morphisms in the fiber category: morphisms in E that project to identity -/
structure FiberHom (P : E ⥤ C) (c : C) (x y : P⁻¹ c) where
  /-- The underlying morphism in E -/
  hom : (x : E) ⟶ (y : E)
  /-- The morphism projects to identity -/
  over : P.map hom = eqToHom x.over ≫ eqToHom y.over.symm

namespace FiberHom

variable {P : E ⥤ C} {c : C}

@[simp]
lemma over_simplified {x y : P⁻¹ c} (f : FiberHom P c x y) :
    P.map f.hom = eqToHom (x.over.trans y.over.symm) := by
  calc
    P.map f.hom = eqToHom x.over ≫ eqToHom y.over.symm := f.over
    _ = eqToHom (x.over.trans y.over.symm) := by
      simp

end FiberHom

/-- The fiber category over c has objects in the fiber and fiber morphisms -/
instance fiberCategory (P : E ⥤ C) (c : C) : Category (P⁻¹ c) where
  Hom := FiberHom P c
  id x := ⟨𝟙 x.obj, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by simp⟩

/-- A based lift is a morphism in E lying over a morphism in C.
    Given f : c ⟶ d, x over c, y over d, a based lift is g : x ⟶ y with P.map g ~ f -/
structure BasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ c) (y : P⁻¹ d) where
  /-- The underlying morphism in the total category -/
  hom : (x : E) ⟶ (y : E)
  /-- The morphism lies over f -/
  over : P.map hom ≫ eqToHom y.over = eqToHom x.over ≫ f

/-- Notation: `x ⟶[f] y` for based lifts. -/
scoped[HeytingLeanFibred] notation:50 x " ⟶[" f "] " y =>
  _root_.HeytingLean.CategoryTheory.Fibred.BasedLift (P := _) f x y

open scoped HeytingLeanFibred

namespace BasedLift

variable {P : E ⥤ C} {c d e : C}

@[ext]
lemma ext {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {g₁ g₂ : x ⟶[f] y}
    (h : g₁.hom = g₂.hom) : g₁ = g₂ := by
  cases g₁; cases g₂; congr

/-- The projection of a based lift gives f (up to eqToHom) -/
@[simp]
lemma over_base {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : x ⟶[f] y) :
    P.map g.hom = eqToHom x.over ≫ f ≫ eqToHom y.over.symm := by
  -- Post-compose the defining equation of a based lift by the inverse transport back to `P.obj y = d`.
  have h := congrArg (fun k => k ≫ eqToHom y.over.symm) g.over
  simpa [Category.assoc] using h

/-- Identity based lift -/
@[simp]
def id (x : P⁻¹ c) : x ⟶[𝟙 c] x :=
  ⟨𝟙 x.obj, by simp⟩

@[simp]
lemma id_hom {x : P⁻¹ c} : (id x).hom = 𝟙 (x : E) := rfl

/-- Composition of based lifts -/
@[simp]
def comp {f : c ⟶ d} {g : d ⟶ e} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ e}
    (l₁ : x ⟶[f] y) (l₂ : y ⟶[g] z) : x ⟶[f ≫ g] z :=
  ⟨l₁.hom ≫ l₂.hom, by simp⟩

/-- Notation for composition of based lifts -/
scoped[HeytingLeanFibred] infixr:80 " ≫[l] " => _root_.HeytingLean.CategoryTheory.Fibred.BasedLift.comp

@[simp]
lemma comp_hom {f : c ⟶ d} {g : d ⟶ e} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ e}
    (l₁ : x ⟶[f] y) (l₂ : y ⟶[g] z) : (l₁ ≫[l] l₂).hom = l₁.hom ≫ l₂.hom := rfl

/-- Cast a based lift along an equality of base morphisms -/
def cast {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (h : f = f') (g : x ⟶[f] y) : x ⟶[f'] y :=
  ⟨g.hom, by subst h; exact g.over⟩

@[simp]
lemma cast_hom {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (h : f = f') (g : x ⟶[f] y) :
    (cast h g).hom = g.hom := rfl

/-- Tautological based lift from any morphism in E -/
@[simp]
def tauto {x y : E} (g : x ⟶ y) :
    (Fiber.tauto (P := P) x) ⟶[P.map g] (Fiber.tauto y) :=
  ⟨g, by simp⟩

end BasedLift

end HeytingLean.CategoryTheory.Fibred
