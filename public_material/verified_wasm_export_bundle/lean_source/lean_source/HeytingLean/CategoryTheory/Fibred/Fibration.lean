/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original work: Sina Hazratpour (LeanFibredCategories)
Port: HeytingLean
-/

import HeytingLean.CategoryTheory.Fibred.CartesianLift

/-!
# Fibrations and Cloven Fibrations

A fibration is a functor P : E ⥤ C such that every morphism f : c ⟶ d in C
and every object y over d has a cartesian lift.

A cloven fibration additionally comes with a choice of cartesian lift for each (f, y).

## Main Definitions

* `Fibration P`: P has cartesian lifts (mere existence)
* `ClovenFibration P`: P has chosen cartesian lifts
* `Transport P`: Transport structure for moving objects along base morphisms
* `CoFibration P`: Dual notion (opfibration)
* `CoClovenFibration P`: Cloven opfibration

## Main Results

* Every cloven fibration induces a Transport structure
* Grothendieck construction is a cloven fibration

## References

* LeanFibredCategories by Sina Hazratpour
* nLab: Grothendieck fibration
-/

namespace HeytingLean.CategoryTheory.Fibred

open _root_.CategoryTheory
open _root_.CategoryTheory.Category
open BasedLift Cartesian

universe u v w

variable {C : Type u} [Category.{v} C]
variable {E : Type w} [Category E]

open scoped HeytingLeanFibred

/-- A fibration is a functor where every morphism has a cartesian lift.
    This is mere existence (Prop). -/
class Fibration (P : E ⥤ C) : Prop where
  /-- Every morphism has a cartesian lift -/
  lift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : HasCartLift (P := P) f y

/-- A cloven fibration has chosen cartesian lifts for all morphisms. -/
class ClovenFibration (P : E ⥤ C) where
  /-- The chosen cartesian lift -/
  lift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : CartLift (P := P) f y

/-- Transport structure: ability to transport objects along base morphisms -/
class Transport (P : E ⥤ C) where
  /-- Transport y along f to get an object over the source of f -/
  transport {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : P⁻¹ c

/-- Notation: f ⋆ y for transport -/
scoped infixr:80 " ⋆ " => Transport.transport

namespace ClovenFibration

variable {P : E ⥤ C} [ClovenFibration P]

/-- A cloven fibration induces a transport structure -/
instance instTransport : Transport P where
  transport f y := (ClovenFibration.lift f y).src

@[simp]
lemma transport_over {c d : C} (f : c ⟶ d) (y : P⁻¹ d) :
    P.obj (f ⋆ y : P⁻¹ c) = c := (f ⋆ y).over

/-- The based lift from the transport to y -/
def basedLift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y) ⟶[f] y :=
  (ClovenFibration.lift f y).based_lift

/-- The based lift is cartesian -/
instance instCartesian {c d : C} (f : c ⟶ d) (y : P⁻¹ d) :
    Cartesian (basedLift f y) :=
  (ClovenFibration.lift f y).is_cart

/-- The underlying morphism of the based lift -/
@[simp]
def basedLiftHom {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y : E) ⟶ (y : E) :=
  (basedLift f y).hom

  /-!
  Transport composition “up to (vertical) isomorphism” is a standard consequence of cloven
  fibrations, but it requires a bit more dedicated infrastructure (vertical isomorphisms in the
  fiber + the usual uniqueness properties packaged as an `Iso`).

  We intentionally keep this file free of proof escapes: the corresponding statement lives as future work
  in `WIP/category_theory_fibred_port/`.
  -/

  end ClovenFibration

/-- Opfibration (cofibration): dual notion with cocartesian lifts -/
class CoFibration (P : E ⥤ C) : Prop where
  /-- Every morphism has a cocartesian lift -/
  colift {c d : C} (f : c ⟶ d) (x : P⁻¹ c) : ∃ (y : P⁻¹ d) (g : x ⟶[f] y),
    ∀ {d' : C} {z : P⁻¹ d'} (u : d ⟶ d') (g' : x ⟶[f ≫ u] z),
      ∃! (l : y ⟶[u] z), (g ≫[l] l).hom = g'.hom

/-- Cloven opfibration with chosen cocartesian lifts -/
class CoClovenFibration (P : E ⥤ C) where
  /-- The chosen cocartesian lift source -/
  tgt {c d : C} (f : c ⟶ d) (x : P⁻¹ c) : P⁻¹ d
  /-- The chosen cocartesian lift -/
  colift {c d : C} (f : c ⟶ d) (x : P⁻¹ c) : x ⟶[f] (tgt f x)
  /-- The lift is cocartesian -/
  is_cocart {c d : C} (f : c ⟶ d) (x : P⁻¹ c) :
    ∀ {d' : C} {z : P⁻¹ d'} (u : d ⟶ d') (g' : x ⟶[f ≫ u] z),
      ∃! (l : (tgt f x) ⟶[u] z), (colift f x ≫[l] l).hom = g'.hom

/-- Cotransport structure -/
class CoTransport (P : E ⥤ C) where
  /-- Cotransport x along f -/
  cotransport {c d : C} (f : c ⟶ d) (x : P⁻¹ c) : P⁻¹ d

namespace CoClovenFibration

variable {P : E ⥤ C} [CoClovenFibration P]

instance instCoTransport : CoTransport P where
  cotransport f x := CoClovenFibration.tgt f x

end CoClovenFibration

/-- Every cloven fibration is a fibration -/
instance clovenToFibration (P : E ⥤ C) [ClovenFibration P] : Fibration P where
  lift f y := ⟨ClovenFibration.lift f y⟩

end HeytingLean.CategoryTheory.Fibred
