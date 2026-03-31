import HeytingLean.Crypto.NECP.AlexandrovRepair

namespace HeytingLean.Tests.Crypto.NECP.AlexandrovRepairSanity

open HeytingLean.Crypto.NECP
open HeytingLean.Crypto.NECP.AlexandrovOpen

#check AlexandrovOpen
#check principalOpen
#check inducedOpenMap
#check inducedOpenNucleus
#check (inferInstance : CompleteLattice (AlexandrovOpen Nat))
#check (inferInstance : Order.Frame (AlexandrovOpen Nat))

end HeytingLean.Tests.Crypto.NECP.AlexandrovRepairSanity
