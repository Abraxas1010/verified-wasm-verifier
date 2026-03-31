import HeytingLean.Crypto.DSA.MLDSASpec

namespace HeytingLean.Tests.Crypto.PQCDSASpecSanity

open HeytingLean.Crypto.DSA.FIPS204

def zeroPoly (p : MLDSA204Params) : Poly p := fun _ => 0

def zeroPolyVec (p : MLDSA204Params) (m : Nat) : PolyVec p m := fun _ => zeroPoly p

def trivialSpec (p : MLDSA204Params) : Spec p where
  keygen := fun _seed => ({ bytes := ByteArray.mk #[] }, { bytes := ByteArray.mk #[] })
  pkRepr := fun _pk =>
    { rho := ByteArray.mk #[]
      t1 := zeroPolyVec p p.k }
  skRepr := fun _sk =>
    { rho := ByteArray.mk #[]
      key := ByteArray.mk #[]
      tr := ByteArray.mk #[]
      s1 := zeroPolyVec p p.ℓ
      s2 := zeroPolyVec p p.k
      t0 := zeroPolyVec p p.k }
  sigRepr := fun _σ =>
    { challengeSeed := ByteArray.mk #[]
      z := zeroPolyVec p p.ℓ
      hintWeight := 0 }
  sign := fun _sk _msg =>
    { attemptSeed := ByteArray.mk #[]
      signature? := some { bytes := ByteArray.mk #[] }
      aborted := false
      aborts_exact := by rfl }
  verify := fun _pk _msg _σ => true
  keygen_rho_matches := by
    intro _seed
    rfl
  verify_hint_bound := by
    intro _pk _msg _σ _hverify
    exact Nat.zero_le p.ω
  verify_sign := by
    intro _seed _msg _pk _sk result _hkeygen _hsign
    cases _hsign
    simp

end HeytingLean.Tests.Crypto.PQCDSASpecSanity
