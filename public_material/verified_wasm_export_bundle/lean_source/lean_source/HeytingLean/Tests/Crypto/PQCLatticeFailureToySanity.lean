import HeytingLean.Crypto.KEM.MLKEMFailureToy

namespace HeytingLean.Tests.Crypto.PQCLatticeFailureToySanity

open HeytingLean.Crypto.KEM.FailureToy
open HeytingLean.Crypto.Lattice.CBDCounts

example : totalCount exCounts = 65536 :=
  ex_totalCount

example : tailCount exCounts 6 * 64 ≤ totalCount exCounts :=
  ex_tailCount_t6

end HeytingLean.Tests.Crypto.PQCLatticeFailureToySanity
