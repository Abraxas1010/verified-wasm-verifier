import HeytingLean.LoF.Combinators.Category.SpanTricategoryThin
import HeytingLean.LoF.Combinators.Category.BranchialBicategory

/-!
# SKYSpanTricategoryThinSanity

Sanity checks for the thin 3-cell layer on span 2-cells (`Span3Cell`), and its use in the
branchial-span substrate.
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

namespace SKYSpanTricategoryThinSanity

def t₁ : Comb := .K
def u₁ : Comb := .S

-- A branchial common-ancestor span is a 1-cell in the span bicategory.
noncomputable def S₁ : (LAncObj t₁ ⟶ LAncObj u₁) :=
  Branchial.lCommonSpan t₁ u₁

-- 2-cells between spans are span maps; the identity 2-cell exists.
noncomputable def η : S₁ ⟶ S₁ := 𝟙 S₁

-- 3-cells between 2-cells are equalities.
#check SpanType.Span3Cell η η

-- Reflexive 3-cell.
example : SpanType.Span3Cell η η := by
  exact SpanType.Span3Cell.refl η

end SKYSpanTricategoryThinSanity

end LoF
end Tests
end HeytingLean
