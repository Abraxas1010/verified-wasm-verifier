import HeytingLean.LoF.Combinators.Category.CompletionBicategory
import HeytingLean.LoF.Combinators.Category.CompletionCells

/-!
# Smoke test: bicategory of SKY paths up to completion homotopy

This file checks that:
- `MWObj` carries a bicategory structure with 2-cells given by completion homotopy, and
- any completion cell yields a 2-morphism between its two boundary paths.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

-- The bicategory instance exists.
#check (inferInstance : Bicategory MWObj)
#check skyCompletionBicategory

example {t : Comb} (c : Completion t) :
    PLift
      (CompletionHomotopy
        (Completion.leftPath c)
        (Completion.rightPath c)) :=
  PLift.up (CompletionHomotopy.of_completion c)

end LoF
end Tests
end HeytingLean
