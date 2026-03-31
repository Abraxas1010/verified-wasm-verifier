import HeytingLean.Crypto.KEM.MLKEMResidualAccurate
import HeytingLean.Crypto.KEM.MLKEMResidualNTTBridge
import HeytingLean.Crypto.KEM.MLKEMMultiCoeffFailure

namespace HeytingLean.Tests.Crypto.PQCLatticeResidualAccurateSanity

open HeytingLean.Crypto.KEM.FIPS203.ResidualAccurate
open HeytingLean.Crypto.KEM.FIPS203.MultiCoeff

example : unionBoundQ 256 (1 / 256 : ℚ) = 1 := by
  norm_num [unionBoundQ]

end HeytingLean.Tests.Crypto.PQCLatticeResidualAccurateSanity
