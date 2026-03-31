import HeytingLean.Util.SHA3
import HeytingLean.LeanCP.RealWorld.CtEqVerified
import HeytingLean.Crypto.KEM.MLKEMAxioms
import HeytingLean.Crypto.KEM.MLKEMSecurity

namespace HeytingLean
namespace LeanCP
namespace RealWorld
namespace MLKEMFOVerified

open HeytingLean.Crypto

private def mkBA (xs : Array UInt8) : ByteArray := ByteArray.mk xs

private def baAppend (a b : ByteArray) : ByteArray :=
  mkBA (a.data ++ b.data)

private def takeBytes (n : Nat) (bytes : ByteArray) : ByteArray :=
  mkBA (bytes.data.extract 0 n)

private def dropBytes (n : Nat) (bytes : ByteArray) : ByteArray :=
  mkBA (bytes.data.extract n bytes.size)

/-- Bytewise mismatch count, mirroring the equality-spec surface of `ct_eq`. -/
def byteMismatchCount : List UInt8 → List UInt8 → Nat
  | [], [] => 0
  | x :: xs, y :: ys => (if x = y then 0 else 1) + byteMismatchCount xs ys
  | _ :: xs, [] => xs.length + 1
  | [], _ :: ys => ys.length + 1

theorem byteMismatchCount_eq_zero_iff {xs ys : List UInt8} :
    byteMismatchCount xs ys = 0 ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp [byteMismatchCount]
      | cons y ys => simp [byteMismatchCount]
  | cons x xs ih =>
      cases ys with
      | nil => simp [byteMismatchCount]
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            simp [byteMismatchCount, ih]
          · simp [byteMismatchCount, hxy]

/-- Pure ciphertext-equality flag matching the verified `ct_eq` mismatch-count semantics. -/
def ctEqByteArrayFlag (lhs rhs : ByteArray) : Nat :=
  if byteMismatchCount lhs.data.toList rhs.data.toList = 0 then 1 else 0

theorem ctEqByteArrayFlag_eq_one_iff (lhs rhs : ByteArray) :
    ctEqByteArrayFlag lhs rhs = 1 ↔ lhs.data.toList = rhs.data.toList := by
  unfold ctEqByteArrayFlag
  by_cases hZero : byteMismatchCount lhs.data.toList rhs.data.toList = 0
  · constructor
    · intro _
      exact (byteMismatchCount_eq_zero_iff).1 hZero
    · intro _
      simp [hZero]
  · constructor
    · intro h
      simp [hZero] at h
    · intro hEq
      have : byteMismatchCount lhs.data.toList rhs.data.toList = 0 :=
        (byteMismatchCount_eq_zero_iff).2 hEq
      contradiction

theorem ctEqByteArrayFlag_eq_zero_of_ne (lhs rhs : ByteArray)
    (hNe : lhs.data.toList ≠ rhs.data.toList) :
    ctEqByteArrayFlag lhs rhs = 0 := by
  unfold ctEqByteArrayFlag
  by_cases hZero : byteMismatchCount lhs.data.toList rhs.data.toList = 0
  · have hEq : lhs.data.toList = rhs.data.toList := (byteMismatchCount_eq_zero_iff).1 hZero
    exact False.elim (hNe hEq)
  · simp [hZero]

/-- `H` in FIPS 203 Section 6 is SHA3-256 on the encapsulation key. -/
def hashH (ek : ByteArray) : ByteArray :=
  Util.SHA3.sha3_256 ek

/-- `G` in FIPS 203 Section 6 is SHA3-512, split into key material and coins. -/
def deriveKeyAndCoins (msg hashEk : ByteArray) : ByteArray × ByteArray :=
  let digest := Util.SHA3.sha3_512 (baAppend msg hashEk)
  (takeBytes 32 digest, dropBytes 32 digest)

/-- `J` in FIPS 203 Section 6 is SHAKE256 applied to the reject seed and ciphertext. -/
def implicitRejectKey (z c : ByteArray) : ByteArray :=
  Util.SHA3.shake256 (baAppend z c) 32

/-- Arithmetic-free witness form of ML-KEM decapsulation's final FO selection step. -/
def decapsFromWitness (mPrime hashEk z c cPrime : ByteArray) : ByteArray :=
  let (kGood, _coins) := deriveKeyAndCoins mPrime hashEk
  let kBad := implicitRejectKey z c
  let flag := ctEqByteArrayFlag c cPrime
  if flag = 0 then kBad else kGood

theorem decapsFromWitness_eq_candidate_of_match
    (mPrime hashEk z c : ByteArray) :
    decapsFromWitness mPrime hashEk z c c = (deriveKeyAndCoins mPrime hashEk).1 := by
  unfold decapsFromWitness
  have hFlag : ctEqByteArrayFlag c c = 1 := by
    exact (ctEqByteArrayFlag_eq_one_iff c c).2 rfl
  simp [hFlag]

theorem decapsFromWitness_eq_reject_of_mismatch
    (mPrime hashEk z c cPrime : ByteArray)
    (hNe : c.data.toList ≠ cPrime.data.toList) :
    decapsFromWitness mPrime hashEk z c cPrime = implicitRejectKey z c := by
  unfold decapsFromWitness
  have hFlag : ctEqByteArrayFlag c cPrime = 0 := ctEqByteArrayFlag_eq_zero_of_ne c cPrime hNe
  simp [hFlag]

/-- Imported proof-line witness paired with the local constant-time comparison audit. -/
structure DecapsulationWitness (p : Crypto.KEM.FIPS203.MLKEM203Params) where
  importedINDCCA : HeytingLean.Crypto.KEM.FIPS203.ProofLine.StatementBundle p
  comparisonAudit : NoBranch ctEqBody

noncomputable def witness (p : Crypto.KEM.FIPS203.MLKEM203Params) : DecapsulationWitness p :=
  { importedINDCCA := Crypto.KEM.FIPS203.mlkem_ind_cca_assumed p
    comparisonAudit := ctEq_noBranch }

theorem witness_parameterSet (p : Crypto.KEM.FIPS203.MLKEM203Params) :
    (witness p).importedINDCCA.parameterSet = p.name := by
  rfl

end MLKEMFOVerified
end RealWorld
end LeanCP
end HeytingLean
