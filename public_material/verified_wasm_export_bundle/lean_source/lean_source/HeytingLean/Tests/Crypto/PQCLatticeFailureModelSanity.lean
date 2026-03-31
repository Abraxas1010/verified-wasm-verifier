import HeytingLean.Crypto.KEM.MLKEMFailureModel

namespace HeytingLean.Tests.Crypto.PQCLatticeFailureModelSanity

open HeytingLean.Crypto.KEM.FIPS203.FailureModel
open HeytingLean.Crypto.Lattice.CBDCounts

example : totalCount smallResidual > 0 :=
  smallResidual_total_nonzero

end HeytingLean.Tests.Crypto.PQCLatticeFailureModelSanity
