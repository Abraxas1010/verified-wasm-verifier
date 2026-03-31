import HeytingLean.Crypto.DSA.MLDSA
import HeytingLean.Crypto.DSA.MLDSA204Params
import HeytingLean.Crypto.KEM.MLKEM
import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.RNG.Seeded
import HeytingLean.Crypto.VerifiedPQC.Programs
import HeytingLean.Crypto.VerifiedPQC.RuntimeBoundary
import HeytingLean.Util.SHA

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

open HeytingLean.Crypto
open HeytingLean.Util

def toToyMLDSAParams (p : DSA.FIPS204.MLDSA204Params) : DSA.MLDSAParams :=
  if p.k = 4 then DSA.mldsa44 else if p.k = 6 then DSA.mldsa65 else DSA.mldsa87

def toyKEMParams (bundle : ParameterBundle) : KEM.MLKEMParams :=
  KEM.FIPS203.toToyMLKEMParams bundle.kem

def toyDSAParams (bundle : ParameterBundle) : DSA.MLDSAParams :=
  toToyMLDSAParams bundle.dsa

private def mkBA (xs : Array UInt8) : ByteArray := ByteArray.mk xs

private def baAppend (a b : ByteArray) : ByteArray :=
  mkBA (a.data ++ b.data)

private def xorBytes (lhs rhs : ByteArray) : ByteArray := Id.run do
  let size := min lhs.size rhs.size
  let mut out : Array UInt8 := #[]
  for i in [0:size] do
    out := out.push (lhs.data[i]! ^^^ rhs.data[i]!)
  return mkBA out

private def keystream (secret : ByteArray) (size : Nat) : ByteArray :=
  (RNG.SeededRNG.nextBytes (RNG.SeededRNG.init secret) size).1

/-- KEM backend interface for the proof/program transport surface. -/
structure KEMOps where
  encap :
    KEM.MLKEMParams → KEM.PublicKey → RNG.SeededRNG →
      KEM.Ciphertext × KEM.SharedSecret × RNG.SeededRNG
  decap :
    KEM.MLKEMParams → KEM.SecretKey → KEM.Ciphertext →
      Except KEM.DecapError KEM.SharedSecret

/-- ML-DSA backend interface for the proof/program transport surface. -/
structure DSAOps where
  signAttached :
    DSA.MLDSAParams → DSA.SecretKey → ByteArray → RNG.SeededRNG →
      DSA.SignedMessage × RNG.SeededRNG
  openSignedMessage :
    DSA.MLDSAParams → DSA.PublicKey → DSA.SignedMessage →
      Except DSA.OpenError ByteArray

/-- Toy stream-seal using the decapsulated secret as a deterministic pad seed. -/
def sealBody (secret body : ByteArray) : ByteArray :=
  xorBytes body (keystream secret body.size)

/-- Symmetric inverse of `sealBody`. -/
def openBody (secret body : ByteArray) : ByteArray :=
  xorBytes body (keystream secret body.size)

/-- Signed manifest binding the packet to the carried certificate lineage. -/
structure Manifest where
  kemCiphertextDigest : ByteArray
  encryptedPayloadDigest : ByteArray
  proofDigest : ByteArray
  verifierProgramHash : String
  deriving DecidableEq

def Manifest.toBytes (manifest : Manifest) : ByteArray :=
  baAppend manifest.kemCiphertextDigest <|
    baAppend manifest.encryptedPayloadDigest <|
      baAppend manifest.proofDigest manifest.verifierProgramHash.toUTF8

/-- Build the manifest implied by the packet contents. -/
def buildManifest (ciphertext : KEM.Ciphertext) (encryptedPayload : ByteArray)
    (certificate : CarriedCertificate) : Manifest :=
  { kemCiphertextDigest := SHA256.sha256Bytes ciphertext.bytes
    encryptedPayloadDigest := SHA256.sha256Bytes encryptedPayload
    proofDigest := certificate.cab.proofCommitment.hash
    verifierProgramHash := certificate.cab.artifact.header.cHash }

/-- Full transmitted packet: encrypted payload plus proof-carrying verifier lineage. -/
structure Packet where
  kemCiphertext : KEM.Ciphertext
  encryptedPayload : ByteArray
  manifest : Manifest
  signedManifest : DSA.SignedMessage
  certificate : CarriedCertificate

/-- Four explicit verification bits routed through the carried acceptance kernel. -/
structure VerificationReport where
  decapOk : Bool
  certificateOk : Bool
  signatureOk : Bool
  manifestOk : Bool
  passedChecks : Nat
  decision : Nat
  deriving DecidableEq, Repr

inductive ReceiveError where
  | decapsulationFailed
  | verificationRejected
  deriving DecidableEq, Repr

def boolToNat (b : Bool) : Nat := if b then 1 else 0

def countPassedChecks (decapOk certificateOk signatureOk manifestOk : Bool) : Nat :=
  boolToNat decapOk + boolToNat certificateOk + boolToNat signatureOk + boolToNat manifestOk

/-- Send a packet under an explicit backend pair. -/
def sendWith (kemOps : KEMOps) (dsaOps : DSAOps) (bundle : ParameterBundle)
    (recipientPk : KEM.PublicKey)
    (senderSk : DSA.SecretKey)
    (payload : ByteArray)
    (certificate : CarriedCertificate)
    (rng : RNG.SeededRNG) :
    Packet × RNG.SeededRNG :=
  let kemParams := toyKEMParams bundle
  let dsaParams := toyDSAParams bundle
  let (ct, ss, rng1) := kemOps.encap kemParams recipientPk rng
  let encryptedPayload := sealBody ss.bytes payload
  let manifest := buildManifest ct encryptedPayload certificate
  let (signedManifest, rng2) := dsaOps.signAttached dsaParams senderSk manifest.toBytes rng1
  ({ kemCiphertext := ct
     encryptedPayload := encryptedPayload
     manifest := manifest
     signedManifest := signedManifest
     certificate := certificate }, rng2)

def verifyPacketWith (kemOps : KEMOps) (dsaOps : DSAOps) (bundle : ParameterBundle)
    (senderPk : DSA.PublicKey)
    (recipientSk : KEM.SecretKey)
    (packet : Packet) : VerificationReport :=
  let kemParams := toyKEMParams bundle
  let dsaParams := toyDSAParams bundle
  match kemOps.decap kemParams recipientSk packet.kemCiphertext with
  | .error _ =>
      let certificateOk := verify packet.certificate
      let passed := countPassedChecks false certificateOk false false
      { decapOk := false
        certificateOk := certificateOk
        signatureOk := false
        manifestOk := false
        passedChecks := passed
        decision := acceptAllChecksFn passed }
  | .ok _ss =>
      let certificateOk := verify packet.certificate
      let signedManifestBytes :=
        match dsaOps.openSignedMessage dsaParams senderPk packet.signedManifest with
        | .ok bytes => bytes
        | .error _ => ByteArray.empty
      let signatureOk := signedManifestBytes == packet.manifest.toBytes
      let manifestOk := packet.manifest = buildManifest packet.kemCiphertext packet.encryptedPayload packet.certificate
      let passed := countPassedChecks true certificateOk signatureOk manifestOk
      { decapOk := true
        certificateOk := certificateOk
        signatureOk := signatureOk
        manifestOk := manifestOk
        passedChecks := passed
        decision := acceptAllChecksFn passed }

/-- Receive succeeds only when all four verifier checks pass. -/
def receiveWith (kemOps : KEMOps) (dsaOps : DSAOps) (bundle : ParameterBundle)
    (senderPk : DSA.PublicKey)
    (recipientSk : KEM.SecretKey)
    (packet : Packet) : Except ReceiveError ByteArray := do
  let report := verifyPacketWith kemOps dsaOps bundle senderPk recipientSk packet
  match kemOps.decap (toyKEMParams bundle) recipientSk packet.kemCiphertext with
  | .error _ => throw .decapsulationFailed
  | .ok ss =>
      if report.decision = 1 then
        return openBody ss.bytes packet.encryptedPayload
      else
        throw .verificationRejected

/-- Promoted send path: callers must supply an explicit backend pair. -/
abbrev sendPromoted := sendWith

/-- Promoted verification path: callers must supply an explicit backend pair. -/
abbrev verifyPacketPromoted := verifyPacketWith

/-- Promoted receive path: callers must supply an explicit backend pair. -/
abbrev receivePromoted := receiveWith

end VerifiedPQC
end Crypto
end HeytingLean
