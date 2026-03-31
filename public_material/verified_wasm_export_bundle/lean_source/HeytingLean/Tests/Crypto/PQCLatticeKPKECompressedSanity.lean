import HeytingLean.Crypto.KEM.MLKEMPKECompressed

/-!
# PQC lattice bridge sanity: K-PKE compression layer (spec-level)

This is a compile-time sanity check: importing `MLKEMPKECompressed` forces the compressed K-PKE
layer to elaborate (without claiming any numerical error bounds).
-/

namespace HeytingLean.Tests.Crypto.PQCLatticeKPKECompressedSanity

open HeytingLean.Crypto.KEM.FIPS203.KPKECompressed

example {p : HeytingLean.Crypto.KEM.FIPS203.MLKEM203Params}
    (codec : HeytingLean.Crypto.KEM.FIPS203.KPKE.MsgCodec p)
    (pk : HeytingLean.Crypto.KEM.FIPS203.KPKE.PublicKey p)
    (sk : HeytingLean.Crypto.KEM.FIPS203.KPKE.SecretKey p)
    (e : HeytingLean.Crypto.KEM.FIPS203.KPKE.ModVec p)
    (ht : pk.t = pk.A.mulVec sk.s + e)
    (m : codec.Msg) (r e1 : HeytingLean.Crypto.KEM.FIPS203.KPKE.ModVec p)
    (e2 : HeytingLean.Crypto.KEM.FIPS203.KPKE.Rq p)
    (hgood :
      codec.good (HeytingLean.Crypto.KEM.FIPS203.KPKE.dot e r + e2
        - HeytingLean.Crypto.KEM.FIPS203.KPKE.dot sk.s e1
        + compressionNoise (p := p) sk (HeytingLean.Crypto.KEM.FIPS203.KPKE.encryptDet codec pk m r e1 e2))) :
    decryptCompressed (p := p) codec sk (encryptCompressed (p := p) codec pk m r e1 e2) = m := by
  simpa using
    (decrypt_encryptCompressed (p := p) (codec := codec) (pk := pk) (sk := sk) (e := e) (ht := ht)
      (m := m) (r := r) (e1 := e1) (e2 := e2) (hgood := hgood))

end HeytingLean.Tests.Crypto.PQCLatticeKPKECompressedSanity

