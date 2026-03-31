import HeytingLean.Crypto.KEM.MLKEMResidualAccurate
import HeytingLean.Crypto.Lattice.NTTConvolution

/-!
# ML-KEM residual: NTT bridge (Gap 3)

This file connects the algorithm-level NTT multiplication proof to the
negacyclic-convolution shape used by the residual model.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

namespace ResidualNTTBridge

open HeytingLean.Crypto.Lattice
open HeytingLean.Crypto.Lattice.NTTConvolution
open HeytingLean.Crypto.Lattice.NTTConvolution.Task5

abbrev q : Nat := 3329
abbrev F : Type := ZMod q

/-- NTT-based multiplication equals negacyclic convolution (coefficient-array form). -/
abbrev ntt_mul_correct_zmod := Task5.ntt_mul_correct

end ResidualNTTBridge

end FIPS203
end KEM
end Crypto
end HeytingLean
