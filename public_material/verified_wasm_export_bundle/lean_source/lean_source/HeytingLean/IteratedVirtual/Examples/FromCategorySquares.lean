import Mathlib.CategoryTheory.CommSq
import HeytingLean.IteratedVirtual.Basic

/-!
# IteratedVirtual.Examples.FromCategorySquares

A nontrivial instance of `VirtualDoubleCategory` from any category `C`:
- vertical arrows are the morphisms of `C`,
- horizontal proarrows are also morphisms of `C`,
- 1-ary cells are commutative squares (`CategoryTheory.CommSq`),
- all other arities are trivial (`PUnit`) for this first-pass example.

This is a deliberately small “bridge” example: it validates that our arity-indexed
`Cell` can carry real structure (commuting squares) without committing to the full
virtual-multicategory composition story yet.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Examples

open CategoryTheory

universe u v

/-- A `VirtualDoubleCategory` built from any category, using `CommSq` for arity-1 cells. -/
def fromCategorySquares (C : Type u) [Category.{v} C] : VirtualDoubleCategory where
  Obj := C
  vertCat := by infer_instance
  Horiz := fun X Y => X ⟶ Y
  Cell := by
    intro n A B vf hf tgt
    cases n with
    | zero =>
        exact PUnit
    | succ n =>
        cases n with
        | zero =>
            -- n = 1
            exact
              PLift <|
                CommSq (C := C)
                  (hf ⟨0, by decide⟩)
                  (vf ⟨0, by decide⟩)
                  (vf ⟨1, by decide⟩)
                  tgt
        | succ _ =>
            -- n ≥ 2: trivial for this first-pass example
            exact PUnit
  horizId := fun X => 𝟙 X

end Examples
end IteratedVirtual
end HeytingLean
