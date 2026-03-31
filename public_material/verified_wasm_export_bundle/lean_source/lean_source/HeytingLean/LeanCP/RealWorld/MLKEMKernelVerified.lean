import HeytingLean.LeanCP.RealWorld.CBDVerified
import HeytingLean.LeanCP.RealWorld.PolyVerified
import HeytingLean.Crypto.KEM.MLKEMPKECompressed

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.Crypto
open NTTVerified

namespace MLKEMKernelVerified

abbrev q : Nat := PolyVerified.q
abbrev polyAddInt := PolyVerified.polyAddInt
abbrev polySubInt := PolyVerified.polySubInt
abbrev polyMulViaNTTInt := PolyVerified.polyMulViaNTTInt
abbrev compressCoeffInt := PolyVerified.compressCoeffInt
abbrev decompressCoeffInt := PolyVerified.decompressCoeffInt

def sampleSecretPoly (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) : Array Int :=
  CBDVerified.sampleSecretPoly p words

def sampleNoisePoly (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) : Array Int :=
  CBDVerified.sampleNoisePoly p words

theorem kernel_modulus_eq (p : KEM.FIPS203.MLKEM203Params)
    (hp : KEM.FIPS203.validParams p) :
    p.q = q := by
  rcases hp with ⟨-, hq, -, -, -, -, -, -⟩
  simpa [q] using hq

theorem sampleSecretPoly_size (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) :
    (sampleSecretPoly p words).size = 256 := by
  simpa [sampleSecretPoly] using CBDVerified.sampleSecretPoly_size p words

theorem sampleNoisePoly_size (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) :
    (sampleNoisePoly p words).size = 256 := by
  simpa [sampleNoisePoly] using CBDVerified.sampleNoisePoly_size p words

theorem sampleSecretPoly_coeff_natAbs_le (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) (i : Nat)
    (hi : i < (sampleSecretPoly p words).size) :
    Int.natAbs ((sampleSecretPoly p words).getD i 0) ≤ p.eta1 := by
  simpa [sampleSecretPoly] using CBDVerified.sampleSecretPoly_coeff_natAbs_le p words i hi

theorem sampleNoisePoly_coeff_natAbs_le (p : KEM.FIPS203.MLKEM203Params) (words : Array Nat) (i : Nat)
    (hi : i < (sampleNoisePoly p words).size) :
    Int.natAbs ((sampleNoisePoly p words).getD i 0) ≤ p.eta2 := by
  simpa [sampleNoisePoly] using CBDVerified.sampleNoisePoly_coeff_natAbs_le p words i hi

theorem polyMul_refines (a b : Array Int) :
    fieldArray256 (polyMulViaNTTInt a b) =
      Crypto.Lattice.NTTConvolution.Task5.negacyclicConv (fieldArray256 a) (fieldArray256 b)
        (fieldArray256_size a) (fieldArray256_size b) :=
  PolyVerified.polyMulViaNTTInt_refines a b

theorem coeffToField_decompressCoeffInt (d : Nat) (x : Fin (2 ^ d)) :
    coeffToField (decompressCoeffInt d x) =
      KEM.FIPS203.Compress.decompress (q := q) d x := by
  exact PolyVerified.coeffToField_decompressCoeffInt d x

theorem decryptCompressed_recovers
    {p : KEM.FIPS203.MLKEM203Params}
    (codec : KEM.FIPS203.KPKE.MsgCodec p)
    (pk : KEM.FIPS203.KPKE.PublicKey p)
    (sk : KEM.FIPS203.KPKE.SecretKey p)
    (e : KEM.FIPS203.KPKE.ModVec p)
    (ht : pk.t = pk.A.mulVec sk.s + e)
    (m : codec.Msg)
    (r e1 : KEM.FIPS203.KPKE.ModVec p)
    (e2 : KEM.FIPS203.KPKE.Rq p)
    (hgood :
      codec.good
        (KEM.FIPS203.KPKE.dot e r + e2 - KEM.FIPS203.KPKE.dot sk.s e1
          + KEM.FIPS203.KPKECompressed.compressionNoise (p := p) sk
              (KEM.FIPS203.KPKE.encryptDet codec pk m r e1 e2))) :
    KEM.FIPS203.KPKECompressed.decryptCompressed (p := p) codec sk
      (KEM.FIPS203.KPKECompressed.encryptCompressed (p := p) codec pk m r e1 e2) = m := by
  exact KEM.FIPS203.KPKECompressed.decrypt_encryptCompressed
    (codec := codec) (pk := pk) (sk := sk) (e := e) (ht := ht)
    (m := m) (r := r) (e1 := e1) (e2 := e2) hgood

end MLKEMKernelVerified

end HeytingLean.LeanCP.RealWorld
