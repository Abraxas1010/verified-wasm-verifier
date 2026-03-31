import HeytingLean.Crypto.QKD.BB84

/-!
# BB84 Sanity Tests

Verifies that the BB84 API is correctly wired.
-/

namespace HeytingLean.Tests.Crypto.BB84Sanity

open HeytingLean.Crypto.QKD.BB84
open HeytingLean.Crypto.QKD.BB84.BB84State

-- State space
#check BB84State
#check ket0
#check ketPlus
#check zBasisStates
#check xBasisStates

-- Tasks
#check copyZ
#check copyX
#check copyAll

-- Constructor model
#check bb84TaskCT
#check BB84Ctor
#check BB84Implements

-- Key impossibility
#check copyAll_impossible
#check not_implements_copyAll

-- Superinformation medium
#check bb84Superinfo
#check zBasisInfo
#check xBasisInfo

-- Security theorems
#check bb84_secure
#check intercept_resend_impossible
#check bb84_composed_security

-- UC reduction hook
#check bb84_uc_secure

end HeytingLean.Tests.Crypto.BB84Sanity

