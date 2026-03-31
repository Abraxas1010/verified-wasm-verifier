import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Action

/-!
# GU.Groupoids (category-theoretic scaffold)

GU motivates (at a high level) Lie groupoids / groupoid semantics for local symmetries.
Mathlib provides abstract groupoids; “Lie” structure is a future refinement.
-/

namespace HeytingLean
namespace GU

open CategoryTheory

universe u v

abbrev Groupoid (Obj : Type u) : Type (max u (v + 1)) :=
  CategoryTheory.Groupoid.{v} Obj

/-- The action groupoid of a group action `G ↻ X`. -/
abbrev ActionGroupoid (G : Type v) (X : Type (max u v)) [Group G] [MulAction G X] : Type (max u v) :=
  CategoryTheory.ActionCategory G X

/--
A lightweight Lie-groupoid package: an abstract groupoid plus a chart-dimension
assignment for object-local smooth models.

This remains intentionally minimal but fully concrete:
consumers can use `chartDim` as a finite-dimensional smoothness index.
-/
structure LieGroupoid (Obj : Type u) where
  toGroupoid : Groupoid Obj
  chartDim : Obj → Nat := fun _ => 0

attribute [instance] LieGroupoid.toGroupoid

end GU
end HeytingLean
