import HeytingLean.Crypto.KEM.MLKEMPKE

/-!
# PQC lattice bridge sanity: K-PKE correctness (spec-level)

This is a compile-time sanity check: importing `MLKEMPKE` forces the K-PKE algebraic layer and its
correctness lemma to elaborate as part of the default build umbrella.
-/

namespace HeytingLean.Tests.Crypto.PQCLatticeKPKESanity

open HeytingLean.Crypto.KEM.FIPS203.KPKE

example {p : HeytingLean.Crypto.KEM.FIPS203.MLKEM203Params} (codec : MsgCodec p) (pk : PublicKey p)
    (sk : SecretKey p)
    (e : ModVec p) (ht : pk.t = pk.A.mulVec sk.s + e)
    (m : codec.Msg) (r e1 : ModVec p) (e2 : Rq p)
    (hgood : codec.good (dot e r + e2 - dot sk.s e1)) :
    decrypt codec sk (encryptDet codec pk m r e1 e2) = m := by
  simpa using
    (decrypt_encryptDet (codec := codec) (pk := pk) (sk := sk) (e := e) (ht := ht) (m := m)
      (r := r) (e1 := e1) (e2 := e2) (hgood := hgood))

end HeytingLean.Tests.Crypto.PQCLatticeKPKESanity
