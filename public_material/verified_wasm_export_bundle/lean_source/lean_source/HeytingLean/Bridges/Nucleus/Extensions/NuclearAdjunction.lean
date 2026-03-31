import Mathlib.CategoryTheory.Adjunction.Basic

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

open CategoryTheory

universe u v w z

/-- Minimal package for an adjunction between two categories. -/
structure AdjunctionPackage (C : Type u) (D : Type w)
    [Category.{v} C] [Category.{z} D] where
  F : C ⥤ D
  G : D ⥤ C
  adj : F ⊣ G

/-- Scoped notion of a nuclear adjunction: monadic + comonadic core predicates. -/
structure NuclearAdjunction (C : Type u) (D : Type w)
    [Category.{v} C] [Category.{z} D] where
  pkg : AdjunctionPackage C D
  monadicCore : Prop
  comonadicCore : Prop

namespace NuclearAdjunction

variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{z} D]

/-- Predicate view of nuclearity. -/
def isNuclear (N : NuclearAdjunction C D) : Prop :=
  N.monadicCore ∧ N.comonadicCore

/-- Identity adjunction package on any category. -/
def identityPackage (C : Type u) [Category.{v} C] : AdjunctionPackage C C where
  F := 𝟭 C
  G := 𝟭 C
  adj := Adjunction.id

/-- Canonical nuclear adjunction witness for the identity adjunction. -/
def identityNuclear (C : Type u) [Category.{v} C] : NuclearAdjunction C C where
  pkg := identityPackage (C := C)
  monadicCore := True
  comonadicCore := True

@[simp] theorem identity_isNuclear (C : Type u) [Category.{v} C] :
    (identityNuclear (C := C)).isNuclear := by
  simp [identityNuclear, isNuclear]

/-- Street-style core extraction scaffold (idempotent by definition in v1). -/
def streetLikeCore (T : C ⥤ C) : C ⥤ C := T

@[simp] theorem streetLikeCore_idempotent (T : C ⥤ C) :
    streetLikeCore (streetLikeCore T) = streetLikeCore T := rfl

end NuclearAdjunction

end Extensions
end Nucleus
end Bridges
end HeytingLean
