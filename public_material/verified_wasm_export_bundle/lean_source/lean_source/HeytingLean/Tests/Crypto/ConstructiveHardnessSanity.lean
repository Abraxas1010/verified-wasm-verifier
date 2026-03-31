import HeytingLean.Crypto.ConstructiveHardnessCore
import HeytingLean.Crypto.ConstructiveHardness.TaskSpec
import HeytingLean.Crypto.ConstructiveHardness.Security
import HeytingLean.Crypto.ConstructiveHardness.Composition
import HeytingLean.Constructor.CT.TaskExistence

namespace HeytingLean.Tests.Crypto.ConstructiveHardnessSanity

open HeytingLean.Crypto.ConstructiveHardness
open HeytingLean.LoF.CryptoSheaf.Quantum
open HeytingLean.Constructor.CT

-- Key theorems and witness are in scope.
#check contextuality_implies_physImpossible
#check PropCT.contextuality_implies_no_constructor
#check triangle_no_global
#check triangle_physImpossible
#check TaskSpec
#check TaskSpec.toPhysicalModality
#check contextuality_implies_task_impossible
#check superinfo_secure_against_eavesdropping
#check composed_security

-- Trivial “physical modality” for compile-time sanity.
def idModality : PhysicalModality where
  toFun := id
  mono := by
    intro P Q hPQ
    exact hPQ
  sound := by
    intro P hP
    exact hP

#check idModality

end HeytingLean.Tests.Crypto.ConstructiveHardnessSanity
