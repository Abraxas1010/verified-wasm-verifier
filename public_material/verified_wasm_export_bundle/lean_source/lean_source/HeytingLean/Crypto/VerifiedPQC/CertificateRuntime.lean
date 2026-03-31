import HeytingLean.Crypto.DSA.MLDSAStandardRuntime
import HeytingLean.Crypto.VerifiedPQC.Certificate
import HeytingLean.Crypto.VerifiedPQC.Serialization

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

open HeytingLean.Crypto

/-- Native authenticated witness over the existing carried certificate envelope. -/
structure SignedCertificateWitness where
  certificate : CarriedCertificate
  signerPublicKey : DSA.PublicKey
  signature : ByteArray

/-- Fresh signing output for a carried certificate witness. -/
structure FreshSignedCertificateWitness where
  signerPublicKey : DSA.PublicKey
  signerSecretKey : DSA.SecretKey
  witness : SignedCertificateWitness

/-- Verification report for the native signed-certificate witness. -/
structure SignedCertificateWitnessReport where
  baseCertificateOk : Bool
  signatureOk : Bool
  decision : Nat
  deriving DecidableEq, Repr

def SignedCertificateWitness.envelopeBytes (w : SignedCertificateWitness) : ByteArray :=
  (CertificateEnvelope.ofCertificate w.certificate).toBytes

def SignedCertificateWitness.signatureShapeOk
    (p : DSA.FIPS204.MLDSA204Params) (w : SignedCertificateWitness) : Bool :=
  DSA.FIPS204.StandardRuntime.checkDetachedSignature p w.signature

def signedCertificateWitnessDecision (baseCertificateOk signatureOk : Bool) : Nat :=
  if baseCertificateOk && signatureOk then 1 else 0

theorem signedCertificateWitnessDecision_eq_one_iff (baseCertificateOk signatureOk : Bool) :
    signedCertificateWitnessDecision baseCertificateOk signatureOk = 1 ↔
      baseCertificateOk = true ∧ signatureOk = true := by
  by_cases hb : baseCertificateOk <;> by_cases hs : signatureOk <;>
    simp [signedCertificateWitnessDecision, hb, hs]

def signCertificateWithStandardRuntime (p : DSA.FIPS204.MLDSA204Params)
    (certificate : CarriedCertificate) (seedHex : String := "") :
    IO (Except String FreshSignedCertificateWitness) := do
  let envelopeBytes := (CertificateEnvelope.ofCertificate certificate).toBytes
  match ← DSA.FIPS204.StandardRuntime.keygenSignDetached p envelopeBytes seedHex with
  | .error e => pure (.error e)
  | .ok signed =>
      pure (.ok
        { signerPublicKey := { bytes := signed.publicKey }
          signerSecretKey := { bytes := signed.secretKey }
          witness :=
            { certificate := certificate
              signerPublicKey := { bytes := signed.publicKey }
              signature := signed.signature } })

def verifySignedCertificateWithStandardRuntime (p : DSA.FIPS204.MLDSA204Params)
    (w : SignedCertificateWitness) : IO SignedCertificateWitnessReport := do
  let baseCertificateOk := VerifiedPQC.verify w.certificate
  let signatureOk ←
    if !w.signatureShapeOk p then
      pure false
    else
      match ←
          DSA.FIPS204.StandardRuntime.verifyDetached
            p w.signerPublicKey.bytes w.signature w.envelopeBytes with
      | .ok () => pure true
      | .error _ => pure false
  pure
    { baseCertificateOk := baseCertificateOk
      signatureOk := signatureOk
      decision := signedCertificateWitnessDecision baseCertificateOk signatureOk }

theorem verifySignedCertificateWithStandardRuntime_imp_baseDecision
    (baseCertificateOk signatureOk : Bool) :
    signedCertificateWitnessDecision baseCertificateOk signatureOk = 1 →
      baseCertificateOk = true := by
  intro h
  exact (signedCertificateWitnessDecision_eq_one_iff _ _).1 h |>.left

end VerifiedPQC
end Crypto
end HeytingLean
