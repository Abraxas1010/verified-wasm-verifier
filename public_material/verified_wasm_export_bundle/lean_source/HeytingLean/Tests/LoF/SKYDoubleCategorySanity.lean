import HeytingLean.LoF.Combinators.Category.NFoldCategory

/-!
Compile-only sanity checks for the Phase 3.1 “double category skeleton”.

We build `DoubleCategoryData` from the SKY multiway path category and check that:
- the cell type is inhabited by any commutative square proof (`CommSq`);
- `PathHomotopy` maps to a `CommSq` instance.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

-- The data record exists.
#check skyPathDoubleData

-- A `PathHomotopy` yields a commutative square (by definition).
example (t u : Comb) (p q : LSteps t u) (h : PathHomotopy t u p q) :
    CommSq (C := MWObj)
      (W := ⟨t⟩) (X := ⟨u⟩) (Y := ⟨u⟩) (Z := ⟨h.v⟩)
      (f := p) (g := q) (h := h.r₁) (i := h.r₂) :=
  PathHomotopy.toCommSq h

end LoF
end Tests
end HeytingLean
