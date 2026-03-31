import HeytingLean.LoF.Combinators.Category.BranchialBicategoryTrunc

/-!
# SKYBranchialBicategoryTruncSanity

Sanity checks for the *path-insensitive* (truncated) branchial span packaging.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open scoped CategoryTheory

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

open Branchial

variable {t u v : Comb}

#check LAncObjTrunc t
#check lCommonSpanTrunc t u

noncomputable def composedTrunc : LAncObjTrunc t ⟶ LAncObjTrunc v :=
  lCommonSpanTrunc t u ≫ lCommonSpanTrunc u v

#check composedTrunc

end LoF
end Tests
end HeytingLean
