import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic

import HeytingLean.Layouts.Tuple.Category
import HeytingLean.Layouts.Tuple.Realization

/-!
# Realization functor `Tuple ⥤ Type`

This packages `Mor.eval` as a `CategoryTheory.Functor` from the CuTe `Tuple` category to `Type`.
-/

namespace HeytingLean
namespace Layouts
namespace Tuple

open CategoryTheory

/-- Realization/semantics of the `Tuple` category as a functor into `Type`. -/
def realizationFunctor : Obj ⥤ Type where
  obj S := Fin (Obj.size S)
  map f := f.eval
  map_id := by
    intro S
    funext i
    simpa using (Mor.eval_id (S := S) i)
  map_comp := by
    intro S T U f g
    funext i
    simpa using (Mor.eval_comp (f := f) (g := g) i)

end Tuple
end Layouts
end HeytingLean
