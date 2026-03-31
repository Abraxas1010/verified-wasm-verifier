import HeytingLean.Topos.DimensionalRatchetLossProfile

namespace HeytingLean
namespace Tests
namespace LT

open HeytingLean.Topos.DimensionalRatchet
open LossProfile

#check JoinExact
#check preserve_inf_exact
#check preserve_join_upper_bound
#check preserve_join_exact_of_assumption
#check PreservationMatrix
#check baseMatrix

example : baseMatrix.joinExactUnconditional = false := by
  exact baseMatrix_join_not_unconditional

end LT
end Tests
end HeytingLean
