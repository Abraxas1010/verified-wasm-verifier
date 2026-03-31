import HeytingLean.Equivalence.LogicMatrixCoalgebra

/-!
# Equivalence.LogicMatrixCoalgebra sanity

This file ensures the “logic ≃ matrix ≃ coalgebra” spine compiles and exposes the key theorems.
-/

namespace HeytingLean
namespace Tests
namespace Equivalence

open HeytingLean.Equivalence

-- Basic: the DNF completeness map exists.
#check LoFPrimary.exprQuotEquivTruthSet

-- Basic: LoF semantic equivalence matches Mealy bisimilarity.
#check CoalgebraRep.eqv_iff_mealy_bisimilar

end Equivalence
end Tests
end HeytingLean

