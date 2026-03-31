import Mathlib.CategoryTheory.Groupoid
import HeytingLean.IteratedVirtual.Equipment
import HeytingLean.IteratedVirtual.Examples.FromCategorySquares

/-!
# IteratedVirtual.Examples.FromGroupoidSquares

If the vertical category is a groupoid, we can turn the CommSq-based virtual double category
into a nontrivial `VirtualEquipment`:
- `companion f := f`
- `conjoint f := Groupoid.inv f`
and the unit/counit cells are witnessed by commutative squares using the groupoid identities.

This is the first “real” equipment-like example: conjoints exist because inverses exist.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Examples

open CategoryTheory

universe u v

/-- A `VirtualEquipment` from any groupoid, using commuting squares for arity-1 cells. -/
def fromGroupoidSquares (C : Type u) [Groupoid.{v} C] : VirtualEquipment := by
  classical
  exact
    { toVirtualDoubleCategory := fromCategorySquares (C := C)
      companion := fun {a b} (f : a ⟶ b) => f
      conjoint := fun {a b} (f : a ⟶ b) => Groupoid.inv f
      companionUnit := fun {a b : C} (f : a ⟶ b) =>
        -- CommSq (𝟙 a) (𝟙 a) f f
        PLift.up ⟨by simp [fromCategorySquares]⟩
      companionCounit := fun {a b : C} (f : a ⟶ b) =>
        -- CommSq f f (𝟙 b) (𝟙 b)
        PLift.up ⟨by simp [fromCategorySquares]⟩
      conjointUnit := fun {a b : C} (f : a ⟶ b) =>
        -- CommSq (𝟙 a) f (𝟙 a) (inv f)
        PLift.up ⟨by simp [fromCategorySquares, fin2]⟩
      conjointCounit := fun {a b : C} (f : a ⟶ b) =>
        -- CommSq (inv f) (𝟙 b) f (𝟙 b)
        PLift.up ⟨by simp [fromCategorySquares, fin2]⟩ }

end Examples
end IteratedVirtual
end HeytingLean
