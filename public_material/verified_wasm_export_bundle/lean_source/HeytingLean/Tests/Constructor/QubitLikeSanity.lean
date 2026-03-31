import HeytingLean.Constructor.CT.Examples.QubitLike

namespace HeytingLean.Tests.Constructor.QubitLikeSanity

open HeytingLean.Constructor.CT
open HeytingLean.Constructor.CT.Examples

#check qubitLikeTaskCT
#check qubitLikeSuperinfo

-- Concrete no-cloning witness on the qubit-like substrate.
#check qubitLikeSuperinfo.no_copyXY
#check TaskCT.SuperinformationMedium.no_cloning_union (M := qubitLikeSuperinfo)

end HeytingLean.Tests.Constructor.QubitLikeSanity

