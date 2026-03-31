import HeytingLean.LeanCP.RealWorld.NTTVerified
import HeytingLean.LeanCP.RealWorld.INTTVerified
import HeytingLean.LeanCP.RealWorld.PolyVerified

namespace HeytingLean.Tests.Crypto.LeanCPNTTSanity

open HeytingLean.LeanCP.RealWorld.NTTVerified
open HeytingLean.LeanCP.RealWorld.INTTVerified
open HeytingLean.LeanCP.RealWorld.PolyVerified

#check nttIterativeInt
#check size_nttIterativeInt
#check centered_nttIterativeInt
#check butterfly_step_safe
#check nttIterativeInt_refines
#check inttIterativeInt
#check size_inttIterativeInt
#check centered_inttIterativeInt
#check inttIterativeInt_refines
#check polyAddInt
#check polySubInt
#check basemulInt
#check polyMulViaNTTInt
#check polyMulViaNTTInt_refines
#check compressCoeffInt
#check decompressCoeffInt

end HeytingLean.Tests.Crypto.LeanCPNTTSanity
