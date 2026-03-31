import HeytingLean.CAB.Certified
import HeytingLean.Certified.Program
import HeytingLean.Certified.Transport
import HeytingLean.Util.SHA

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

open HeytingLean.CAB
open HeytingLean.Certified
open HeytingLean.Util

/-- The carried program artifact must internally agree with its advertised C hash. -/
def ArtifactHashConsistent (artifact : ProgramArtifact) : Prop :=
  artifact.header.cHash = SHA256.sha256Hex artifact.cCode.toUTF8

instance (artifact : ProgramArtifact) : Decidable (ArtifactHashConsistent artifact) := by
  unfold ArtifactHashConsistent
  infer_instance

/-- A packet-carried certificate pairs a CAB commitment with the committed proof bytes. -/
structure CarriedCertificate where
  cab : HeytingLean.CAB ProgramArtifact ArtifactHashConsistent
  proofBytes : ByteArray

/-- Recompute the artifact hash from the embedded C code. -/
def artifactHashMatches (cert : CarriedCertificate) : Bool :=
  decide (ArtifactHashConsistent cert.cab.artifact)

/-- Verify both the proof-byte commitment and the artifact/C hash linkage. -/
def verify (cert : CarriedCertificate) : Bool :=
  artifactHashMatches cert && CAB.verify cert.cab cert.proofBytes

theorem artifactHashConsistent_of_certifiedProgram (program : CertifiedProgram) :
    ArtifactHashConsistent program.artifact := by
  simpa [ArtifactHashConsistent] using Certified.Transport.rt2_cHash_matches program

/-- Package a certified program and external proof bytes as a carried certificate. -/
def mkCarriedCertificate (program : CertifiedProgram) (proofBytes : ByteArray)
    (metadata : CABMetadata) : CarriedCertificate :=
  let artifactCertified : HeytingLean.Certified.Certified ProgramArtifact ArtifactHashConsistent :=
    ⟨program.artifact, artifactHashConsistent_of_certifiedProgram program⟩
  let computeHash : ArtifactHashConsistent artifactCertified.val → ProofHash :=
    fun _ => { hash := SHA256.sha256Bytes proofBytes }
  { cab := CAB.fromCertified artifactCertified computeHash metadata
    proofBytes := proofBytes }

theorem verify_mkCarriedCertificate (program : CertifiedProgram) (proofBytes : ByteArray)
    (metadata : CABMetadata) :
    verify (mkCarriedCertificate program proofBytes metadata) = true := by
  unfold verify artifactHashMatches mkCarriedCertificate CAB.verify CAB.fromCertified
  simp [ArtifactHashConsistent]
  exact artifactHashConsistent_of_certifiedProgram program

end VerifiedPQC
end Crypto
end HeytingLean
