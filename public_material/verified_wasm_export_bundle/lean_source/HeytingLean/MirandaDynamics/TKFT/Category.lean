import Mathlib.CategoryTheory.Category.Basic
import HeytingLean.MirandaDynamics.TKFT.Reaching

/-!
# MirandaDynamics.TKFT: reaching relations as a category

The TKFT intuition is that “gluing bordisms” corresponds to composition of reaching semantics.

In this repo we model the semantics level by `ReachingRel α β` (a relation `α → β → Prop`) with:
- identity: equality relation (`ReachingRel.id`),
- composition: relational composition (`ReachingRel.comp`).

This file packages these laws as an actual `Category`, avoiding conflicts with the standard `Type`
category by using a dedicated wrapper for objects.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace TKFT

open CategoryTheory

universe u

/-- A wrapper around a carrier type, used to avoid conflicting with Mathlib’s `Category (Type u)`. -/
structure Obj : Type (u + 1) where
  carrier : Type u

instance : CoeSort Obj (Type u) :=
  ⟨Obj.carrier⟩

instance : Category Obj where
  Hom X Y := ReachingRel X Y
  id X := ReachingRel.id X
  comp f g := ReachingRel.comp f g
  id_comp := by
    intro X Y f
    simpa using congrArg (fun h => h) (ReachingRel.id_left f)
  comp_id := by
    intro X Y f
    simpa using congrArg (fun h => h) (ReachingRel.id_right f)
  assoc := by
    intro W X Y Z f g h
    simpa using congrArg (fun h => h) (ReachingRel.assoc f g h)

end TKFT
end MirandaDynamics
end HeytingLean

