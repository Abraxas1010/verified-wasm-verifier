import HeytingLean.LoF.Combinators.Category.BranchialAncestorFunctor

/-!
# SKYBranchialAncestorFunctorSanity

Sanity checks for the ancestor-object functors relating branchial ancestor types
back to the multiway path category `MWObj`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open scoped CategoryTheory

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

open Branchial

variable {t u : Comb}

#check ancestorsFunctor
#check ancestorsTruncFunctor

#check mapLAncestors
#check mapLAncestorsTrunc

#check commonEquivPullback t u
#check commonTruncEquivPullback t u

end LoF
end Tests
end HeytingLean

