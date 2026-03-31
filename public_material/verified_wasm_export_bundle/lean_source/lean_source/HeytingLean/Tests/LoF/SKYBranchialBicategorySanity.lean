import HeytingLean.LoF.Combinators.Category.BranchialBicategory

/-!
# SKYBranchialBicategorySanity

Sanity checks for the “Type-level” branchial span/bicategory model:

- `SpanType` provides a bicategory of spans in `Type`.
- `Branchial.lCommonSpan` packages common-ancestor data as an actual span in that bicategory.
- `BranchialSpan.equivCommonApex` identifies the witness structure with a point of the span apex.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

open scoped CategoryTheory

open Combinators.Category.SpanType
open Combinators.Category.Branchial

def t : Comb := .K
def u : Comb := .S
def v : Comb := .Y

-- The canonical common-ancestor span is a genuine 1-morphism in the bicategory of spans in `Type`.
#check Branchial.lCommonSpan t u

-- We can compose spans (pullback composition in `Type`).
noncomputable def composed : (Branchial.LAncObj t ⟶ Branchial.LAncObj v) :=
  (Branchial.lCommonSpan t u) ≫ (Branchial.lCommonSpan u v)

#check composed

-- The witness-style `BranchialSpan` is equivalent to a point of the canonical span apex.
#check BranchialSpan.equivCommonApex t u

end LoF
end Tests
end HeytingLean
