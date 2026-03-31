import HeytingLean.Crypto.VerifiedPQC
import HeytingLean.Crypto.VerifiedPQC.ProtocolToy
import HeytingLean.LeanCP.Examples.VerifiedPQCVerifier

namespace HeytingLean.Tests.Crypto.VerifiedPQCSanity

open HeytingLean
open HeytingLean.Crypto
open HeytingLean.Crypto.VerifiedPQC

#check ArtifactHashConsistent
#check CarriedCertificate
#check acceptAllChecksProgram
#check acceptAllChecksCertificate
#check standardRuntimeBundle
#check sendWith
#check verifyPacketPromoted
#check receivePromoted
#check CertificateEnvelope
#check PacketEnvelope
#check HeytingLean.LeanCP.Examples.verifiedPQCVerifier_verified

def sampleBundle : ParameterBundle :=
  { kem := KEM.FIPS203.mlkem512
    dsa := DSA.FIPS204.mldsa44 }

def sampleMessage : ByteArray := "proof-carrying-pq-message".toUTF8
def sampleProofBytes : ByteArray := "leancp-verified-pqc-accept-all-checks-proof".toUTF8

def recipientRng : RNG.SeededRNG := RNG.SeededRNG.init "recipient-seed".toUTF8
def senderRng : RNG.SeededRNG := RNG.SeededRNG.init "sender-seed".toUTF8

def recipientKeys : KEM.PublicKey × KEM.SecretKey × RNG.SeededRNG :=
  KEM.Toy.keygen (toyKEMParams sampleBundle) recipientRng

def senderKeys : DSA.PublicKey × DSA.SecretKey × RNG.SeededRNG :=
  DSA.Toy.keygen (toyDSAParams sampleBundle) senderRng

def sampleCertificate : CarriedCertificate :=
  acceptAllChecksCertificate sampleProofBytes

def sampleRuntimeBundle : RuntimeBundle :=
  standardRuntimeBundle sampleBundle

def samplePacket : Packet :=
  (sendToy sampleBundle recipientKeys.1 senderKeys.2.1 sampleMessage sampleCertificate senderKeys.2.2).1

def sampleReport : VerificationReport :=
  verifyPacketToy sampleBundle senderKeys.1 recipientKeys.2.1 samplePacket

def sampleReceive : Except ReceiveError ByteArray :=
  receiveToy sampleBundle senderKeys.1 recipientKeys.2.1 samplePacket

def sampleCertificateEnvelope : CertificateEnvelope :=
  CertificateEnvelope.ofCertificate sampleCertificate

def samplePacketEnvelope : PacketEnvelope :=
  PacketEnvelope.ofPacket samplePacket

def sampleCertificateEnvelopeRoundtrip : Bool :=
  sampleCertificateEnvelope.roundtripOk

def sampleCertificateEnvelopeTrailingBytesRejected : Bool :=
  sampleCertificateEnvelope.trailingBytesRejected

def sampleCertificateEnvelopeLastByteTruncationRejected : Bool :=
  sampleCertificateEnvelope.lastByteTruncationRejected

def samplePacketEnvelopeRoundtrip : Bool :=
  samplePacketEnvelope.roundtripOk

def samplePacketEnvelopeTrailingBytesRejected : Bool :=
  samplePacketEnvelope.trailingBytesRejected

def samplePacketEnvelopeLastByteTruncationRejected : Bool :=
  samplePacketEnvelope.lastByteTruncationRejected

def samplePacketEnvelopeMatches : Bool :=
  samplePacketEnvelope.matchesPacket samplePacket

def samplePacketEnvelopeManifestOk : Bool :=
  samplePacketEnvelope.manifestOk

def samplePacketEnvelopeCertificateOk : Bool :=
  samplePacketEnvelope.certificateOk

def samplePacketEnvelopeTamperedVerifierHashRejectsManifest : Bool :=
  let tampered := { samplePacketEnvelope with verifierProgramHash := "tampered-program-hash" }
  tampered.manifestOk = false

def samplePacketEnvelopeTamperedProofDigestRejectsManifest : Bool :=
  let tampered := { samplePacketEnvelope with proofDigest := ByteArray.empty }
  tampered.manifestOk = false

def samplePacketEnvelopeTamperedCertificateRejectsCertificate : Bool :=
  let tamperedCert := { sampleCertificateEnvelope with proofBytes := "tampered-proof".toUTF8 }
  let tampered := { samplePacketEnvelope with certificate := tamperedCert }
  tampered.certificateOk = false

def sampleReceiveMatches : Bool :=
  match sampleReceive with
  | .ok bytes => decide (bytes = sampleMessage)
  | .error _ => false

example : verify sampleCertificate = true := by
  native_decide

example : sampleRuntimeBundle.kem.scheme = "ML-KEM-512" := by
  native_decide

example : sampleRuntimeBundle.dsa.scheme = "ML-DSA-44" := by
  native_decide

example : sampleReport.passedChecks = 4 := by
  native_decide

example : sampleReport.decision = 1 := by
  native_decide

example : sampleReceiveMatches = true := by
  native_decide

example : sampleCertificateEnvelope.verify = true := by
  native_decide

example : sampleCertificateEnvelopeRoundtrip = true := by
  native_decide

example : sampleCertificateEnvelopeTrailingBytesRejected = true := by
  native_decide

example : sampleCertificateEnvelopeLastByteTruncationRejected = true := by
  native_decide

example : samplePacketEnvelopeRoundtrip = true := by
  native_decide

example : samplePacketEnvelopeTrailingBytesRejected = true := by
  native_decide

example : samplePacketEnvelopeLastByteTruncationRejected = true := by
  native_decide

example : samplePacketEnvelopeMatches = true := by
  native_decide

example : samplePacketEnvelopeManifestOk = true := by
  native_decide

example : samplePacketEnvelopeCertificateOk = true := by
  native_decide

example : samplePacketEnvelopeTamperedVerifierHashRejectsManifest = true := by
  native_decide

example : samplePacketEnvelopeTamperedProofDigestRejectsManifest = true := by
  native_decide

example : samplePacketEnvelopeTamperedCertificateRejectsCertificate = true := by
  native_decide

end HeytingLean.Tests.Crypto.VerifiedPQCSanity
