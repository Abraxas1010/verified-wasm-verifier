import HeytingLean.LoF.Combinators.Category.BranchialCategory

/-!
Compile-only sanity checks for the branchial path category.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check BranchialObj
#check BranchialPathCat

-- Category instance exists.
example : CategoryTheory.Category BranchialPathCat := by infer_instance

end LoF
end Tests
end HeytingLean

