import HeytingLean.LoF.Combinators.Category.NFoldCategoryArrow
import HeytingLean.LoF.Combinators.Category.CompletionCells

/-!
# Smoke test: iterated Arrow “hypercube tower” for completion-quotiented SKY paths

This file checks that:
- `MWCat n` is a category for all `n`, and
- a completion cell induces a commutative square in the quotient, hence a morphism in `Arrow MWQuotObj`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check MWCat
#check (MWCat 0)
#check (MWCat 1)
#check (MWCat 2)

/-- Any completion cell identifies its two boundary paths in the quotient, hence yields a square
in the arrow category. -/
example {t : Comb} (c : Completion t) :
    let X : MWQuotObj := ⟨t⟩
    let Y : MWQuotObj := ⟨c.w⟩
    let f : X ⟶ Y := Quotient.mk _ (Completion.leftPath c)
    let g : X ⟶ Y := Quotient.mk _ (Completion.rightPath c)
    (CategoryTheory.Arrow.mk f : CategoryTheory.Arrow MWQuotObj) ⟶
      (CategoryTheory.Arrow.mk g : CategoryTheory.Arrow MWQuotObj) := by
  classical
  intro X Y f g
  refine
    CategoryTheory.Arrow.homMk (T := MWQuotObj) (f := CategoryTheory.Arrow.mk f) (g := CategoryTheory.Arrow.mk g)
      (𝟙 X) (𝟙 Y) ?_
  -- Reduce commutativity to an equality of morphisms in the quotient.
  simp
  dsimp [f, g]
  exact (CompletionHomotopy.quot_eq_of_completion (t := t) c).symm

end LoF
end Tests
end HeytingLean

