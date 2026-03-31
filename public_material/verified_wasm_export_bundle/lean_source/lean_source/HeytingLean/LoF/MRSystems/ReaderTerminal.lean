import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import HeytingLean.LoF.MRSystems.Coalgebra

/-!
# Reader coalgebras have a trivial terminal object (Phase E.3, scoped correction)

This module addresses the program spec’s “(M,R) as terminal coalgebra” suggestion by first
checking the simplest candidate functor we already use in `MRSystems/Coalgebra.lean`:

* the **reader** endofunctor `F_A(X) := A → X` on `Type`.

Fact (proved below):
* For any `A`, the coalgebra on `PUnit` is **terminal** in the category of `F_A`-coalgebras.

Interpretation:
* This shows that “terminal coalgebra” is too weak to characterize nontrivial Rosen closure if we
  model `R : B → (A → B)` merely as a reader coalgebra on `Type`.
* Any meaningful terminal-coalgebra characterization of (M,R) closure must therefore refine either:
  - the endofunctor (encode more structure than just `B → A → B`), or
  - the ambient category (impose admissibility/observability constraints).
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open CategoryTheory
open CategoryTheory.Limits

universe u v

/-! ## The terminal reader coalgebra -/

variable (A : Type u)

/-- The (unique) reader-coalgebra structure on `PUnit` for `ReaderEndo A`. -/
def readerUnitCoalgebra : CategoryTheory.Endofunctor.Coalgebra (ReaderEndo.{u, v} A) where
  V := PUnit
  str := fun _u => fun _a => PUnit.unit

/-- `PUnit` is terminal in the category of reader coalgebras. -/
noncomputable def readerUnitCoalgebra_isTerminal :
    IsTerminal (readerUnitCoalgebra A) := by
  refine IsTerminal.ofUniqueHom (Y := readerUnitCoalgebra A)
    (h := fun X => ?_) (uniq := ?_)
  · refine { f := fun _ => PUnit.unit, h := ?_ }
    -- Both sides are functions `X.V → (A → PUnit)`; extensionality closes it.
    funext _x _a
    rfl
  · intro X m
    ext x
    cases m.f x
    rfl

end MRSystems
end LoF
end HeytingLean
