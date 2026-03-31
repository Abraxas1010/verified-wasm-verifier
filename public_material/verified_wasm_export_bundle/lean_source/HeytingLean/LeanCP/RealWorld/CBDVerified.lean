import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.Lattice.CBDCounts

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.Crypto

namespace CBDVerified

/-- Deterministic CBD coefficient sampler from a `2*eta`-bit word. -/
def sampleCoeff (eta : Nat) (word : Nat) : Int :=
  Lattice.CBDCounts.cbdSample eta word

theorem sampleCoeff_natAbs_le (eta : Nat) (word : Nat) :
    Int.natAbs (sampleCoeff eta word) ≤ eta := by
  simpa [sampleCoeff] using Lattice.CBDCounts.cbdSample_natAbs_le eta word

/-- Build a length-256 coefficient array by applying `sampleCoeff` pointwise. -/
def samplePoly (eta : Nat) (words : Array Nat) : Array Int :=
  Array.ofFn (fun i : Fin 256 => sampleCoeff eta (words.getD i.val 0))

theorem samplePoly_size (eta : Nat) (words : Array Nat) :
    (samplePoly eta words).size = 256 := by
  simp [samplePoly]

theorem samplePoly_coeff_natAbs_le (eta : Nat) (words : Array Nat) (i : Nat)
    (hi : i < (samplePoly eta words).size) :
    Int.natAbs ((samplePoly eta words).getD i 0) ≤ eta := by
  have hi256 : i < 256 := by
    simpa [samplePoly] using hi
  simpa [samplePoly, sampleCoeff, Array.getD_eq_getD_getElem?, hi, hi256] using
    Lattice.CBDCounts.cbdSample_natAbs_le eta (words.getD i 0)

def sampleSecretCoeff (p : KEM.FIPS203.MLKEM203Params) (word : Nat) : Int :=
  sampleCoeff p.eta1 word

def sampleNoiseCoeff (p : KEM.FIPS203.MLKEM203Params) (word : Nat) : Int :=
  sampleCoeff p.eta2 word

theorem sampleSecretCoeff_natAbs_le (p : KEM.FIPS203.MLKEM203Params) (word : Nat) :
    Int.natAbs (sampleSecretCoeff p word) ≤ p.eta1 := by
  simpa [sampleSecretCoeff] using sampleCoeff_natAbs_le p.eta1 word

theorem sampleNoiseCoeff_natAbs_le (p : KEM.FIPS203.MLKEM203Params) (word : Nat) :
    Int.natAbs (sampleNoiseCoeff p word) ≤ p.eta2 := by
  simpa [sampleNoiseCoeff] using sampleCoeff_natAbs_le p.eta2 word

def sampleSecretPoly (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) : Array Int :=
  samplePoly p.eta1 words

def sampleNoisePoly (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) : Array Int :=
  samplePoly p.eta2 words

theorem sampleSecretPoly_size (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) :
    (sampleSecretPoly p words).size = 256 := by
  simpa [sampleSecretPoly] using samplePoly_size p.eta1 words

theorem sampleNoisePoly_size (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) :
    (sampleNoisePoly p words).size = 256 := by
  simpa [sampleNoisePoly] using samplePoly_size p.eta2 words

theorem sampleSecretPoly_coeff_natAbs_le (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) (i : Nat)
    (hi : i < (sampleSecretPoly p words).size) :
    Int.natAbs ((sampleSecretPoly p words).getD i 0) ≤ p.eta1 := by
  simpa [sampleSecretPoly] using samplePoly_coeff_natAbs_le p.eta1 words i hi

theorem sampleNoisePoly_coeff_natAbs_le (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) (i : Nat)
    (hi : i < (sampleNoisePoly p words).size) :
    Int.natAbs ((sampleNoisePoly p words).getD i 0) ≤ p.eta2 := by
  simpa [sampleNoisePoly] using samplePoly_coeff_natAbs_le p.eta2 words i hi

end CBDVerified

end HeytingLean.LeanCP.RealWorld
