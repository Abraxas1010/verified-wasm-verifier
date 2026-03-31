import HeytingLean.Crypto.VerifiedPQC.Protocol

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

open HeytingLean.CAB
open HeytingLean.Util

private def mkBA (xs : Array UInt8) : ByteArray := ByteArray.mk xs

private def baAppend (a b : ByteArray) : ByteArray :=
  mkBA (a.data ++ b.data)

private def snocByte (bytes : ByteArray) (b : UInt8) : ByteArray :=
  mkBA (bytes.data.push b)

private def takeBytes (bytes : ByteArray) (n : Nat) : ByteArray :=
  mkBA (bytes.data.extract 0 n)

private def u64BytesLE (u : UInt64) : Array UInt8 :=
  let rec go (k : Nat) (n : Nat) (acc : Array UInt8) : Array UInt8 :=
    match k with
    | 0 => acc
    | k + 1 =>
        let b : UInt8 := UInt8.ofNat (n % 256)
        go k (n / 256) (acc.push b)
  go 8 u.toNat #[]

private def encodeU64LE (u : UInt64) : ByteArray :=
  ByteArray.mk (u64BytesLE u)

private def decodeU64AtLE (bytes : ByteArray) (offset : Nat) : UInt64 :=
  let rec go (i : Nat) (pow : Nat) (acc : Nat) : Nat :=
    if i < 8 then
      let b := bytes.get! (offset + i) |>.toNat
      go (i + 1) (pow * 256) (acc + b * pow)
    else
      acc
  UInt64.ofNat (go 0 1 0)

private def takePrefix? (n : Nat) (bytes : ByteArray) : Option (ByteArray × ByteArray) :=
  if n ≤ bytes.size then
    let head := mkBA (bytes.data.extract 0 n)
    let tail := mkBA (bytes.data.extract n bytes.size)
    some (head, tail)
  else
    none

private def encodeBytes (bytes : ByteArray) : ByteArray :=
  baAppend (encodeU64LE (UInt64.ofNat bytes.size)) bytes

private def decodeBytes? (bytes : ByteArray) : Option (ByteArray × ByteArray) := do
  let (lenBytes, rest) ← takePrefix? 8 bytes
  let len := (decodeU64AtLE lenBytes 0).toNat
  takePrefix? len rest

private def encodeString (s : String) : ByteArray :=
  encodeBytes s.toUTF8

private def decodeString? (bytes : ByteArray) : Option (String × ByteArray) := do
  let (strBytes, rest) ← decodeBytes? bytes
  let s ← String.fromUTF8? strBytes
  pure (s, rest)

private def fragmentToString : Erasure.FragmentId → String
  | .Nat1 => "Nat1"
  | .Nat2 => "Nat2"
  | .List1 => "List1"
  | .Bool1 => "Bool1"
  | .Custom name => s!"Custom({name})"

private def cabDimensionCode : CAB.Dimension → UInt64
  | .D1 => 1
  | .D2 => 2
  | .D3 => 3
  | .D4 => 4

/-- Byte-serializable transport view of the carried verifier certificate. -/
structure CertificateEnvelope where
  programId : String
  programName : String
  programHash : String
  programCode : String
  proofCommitment : ByteArray
  proofBytes : ByteArray
  cabFragment : String
  cabDimension : UInt64
  cabTimestamp : UInt64
  deriving DecidableEq

namespace CertificateEnvelope

def ofCertificate (cert : CarriedCertificate) : CertificateEnvelope :=
  { programId := cert.cab.artifact.header.id
    programName := cert.cab.artifact.header.name
    programHash := cert.cab.artifact.header.cHash
    programCode := cert.cab.artifact.cCode
    proofCommitment := cert.cab.proofCommitment.hash
    proofBytes := cert.proofBytes
    cabFragment := fragmentToString cert.cab.metadata.fragment
    cabDimension := cabDimensionCode cert.cab.metadata.dimension
    cabTimestamp := UInt64.ofNat cert.cab.metadata.timestamp }

/-- Transport-level certificate verification mirroring the carried certificate checks. -/
def verify (env : CertificateEnvelope) : Bool :=
  env.programHash = SHA256.sha256Hex env.programCode.toUTF8 &&
    env.proofCommitment = SHA256.sha256Bytes env.proofBytes

def toBytes (env : CertificateEnvelope) : ByteArray :=
  baAppend (encodeString env.programId) <|
    baAppend (encodeString env.programName) <|
      baAppend (encodeString env.programHash) <|
        baAppend (encodeString env.programCode) <|
          baAppend (encodeBytes env.proofCommitment) <|
            baAppend (encodeBytes env.proofBytes) <|
              baAppend (encodeString env.cabFragment) <|
                baAppend (encodeU64LE env.cabDimension) (encodeU64LE env.cabTimestamp)

def fromBytes? (bytes : ByteArray) : Option CertificateEnvelope := do
  let (programId, r1) ← decodeString? bytes
  let (programName, r2) ← decodeString? r1
  let (programHash, r3) ← decodeString? r2
  let (programCode, r4) ← decodeString? r3
  let (proofCommitment, r5) ← decodeBytes? r4
  let (proofBytes, r6) ← decodeBytes? r5
  let (cabFragment, r7) ← decodeString? r6
  let (cabDimensionBytes, r8) ← takePrefix? 8 r7
  let (cabTimestampBytes, r9) ← takePrefix? 8 r8
  if r9.size = 0 then
    some
      { programId := programId
        programName := programName
        programHash := programHash
        programCode := programCode
        proofCommitment := proofCommitment
        proofBytes := proofBytes
        cabFragment := cabFragment
        cabDimension := decodeU64AtLE cabDimensionBytes 0
        cabTimestamp := decodeU64AtLE cabTimestampBytes 0 }
  else
    none

def roundtripOk (env : CertificateEnvelope) : Bool :=
  fromBytes? env.toBytes == some env

/-- Transport envelope rejects an appended trailing byte instead of silently accepting it. -/
def trailingBytesRejected (env : CertificateEnvelope) : Bool :=
  fromBytes? (snocByte env.toBytes 0) == none

/-- Transport envelope rejects a one-byte truncation of its encoded form. -/
def lastByteTruncationRejected (env : CertificateEnvelope) : Bool :=
  if env.toBytes.size = 0 then
    false
  else
    fromBytes? (takeBytes env.toBytes (env.toBytes.size - 1)) == none

theorem ofCertificate_verify (cert : CarriedCertificate) :
    (ofCertificate cert).verify = VerifiedPQC.verify cert := by
  simp [CertificateEnvelope.ofCertificate, CertificateEnvelope.verify, VerifiedPQC.verify,
    artifactHashMatches, ArtifactHashConsistent, HeytingLean.CAB.verify, eq_comm]

end CertificateEnvelope

/-- Byte-serializable transport view of the transmitted packet. -/
structure PacketEnvelope where
  kemCiphertext : ByteArray
  encryptedPayload : ByteArray
  kemCiphertextDigest : ByteArray
  encryptedPayloadDigest : ByteArray
  proofDigest : ByteArray
  verifierProgramHash : String
  signedManifest : ByteArray
  certificate : CertificateEnvelope
  deriving DecidableEq

namespace PacketEnvelope

def ofPacket (packet : Packet) : PacketEnvelope :=
  { kemCiphertext := packet.kemCiphertext.bytes
    encryptedPayload := packet.encryptedPayload
    kemCiphertextDigest := packet.manifest.kemCiphertextDigest
    encryptedPayloadDigest := packet.manifest.encryptedPayloadDigest
    proofDigest := packet.manifest.proofDigest
    verifierProgramHash := packet.manifest.verifierProgramHash
    signedManifest := packet.signedManifest.bytes
    certificate := CertificateEnvelope.ofCertificate packet.certificate }

def manifest (env : PacketEnvelope) : Manifest :=
  { kemCiphertextDigest := env.kemCiphertextDigest
    encryptedPayloadDigest := env.encryptedPayloadDigest
    proofDigest := env.proofDigest
    verifierProgramHash := env.verifierProgramHash }

def certificateOk (env : PacketEnvelope) : Bool :=
  env.certificate.verify

def manifestOk (env : PacketEnvelope) : Bool :=
  env.kemCiphertextDigest = SHA256.sha256Bytes env.kemCiphertext &&
    env.encryptedPayloadDigest = SHA256.sha256Bytes env.encryptedPayload &&
    env.proofDigest = env.certificate.proofCommitment &&
    env.verifierProgramHash = env.certificate.programHash

def matchesPacket (env : PacketEnvelope) (packet : Packet) : Bool :=
  env == ofPacket packet

def toBytes (env : PacketEnvelope) : ByteArray :=
  baAppend (encodeBytes env.kemCiphertext) <|
    baAppend (encodeBytes env.encryptedPayload) <|
      baAppend (encodeBytes env.kemCiphertextDigest) <|
        baAppend (encodeBytes env.encryptedPayloadDigest) <|
          baAppend (encodeBytes env.proofDigest) <|
            baAppend (encodeString env.verifierProgramHash) <|
              baAppend (encodeBytes env.signedManifest) (encodeBytes env.certificate.toBytes)

def fromBytes? (bytes : ByteArray) : Option PacketEnvelope := do
  let (kemCiphertext, r1) ← decodeBytes? bytes
  let (encryptedPayload, r2) ← decodeBytes? r1
  let (kemCiphertextDigest, r3) ← decodeBytes? r2
  let (encryptedPayloadDigest, r4) ← decodeBytes? r3
  let (proofDigest, r5) ← decodeBytes? r4
  let (verifierProgramHash, r6) ← decodeString? r5
  let (signedManifest, r7) ← decodeBytes? r6
  let (certBytes, r8) ← decodeBytes? r7
  let certificate ← CertificateEnvelope.fromBytes? certBytes
  if r8.size = 0 then
    some
      { kemCiphertext := kemCiphertext
        encryptedPayload := encryptedPayload
        kemCiphertextDigest := kemCiphertextDigest
        encryptedPayloadDigest := encryptedPayloadDigest
        proofDigest := proofDigest
        verifierProgramHash := verifierProgramHash
        signedManifest := signedManifest
        certificate := certificate }
  else
    none

def roundtripOk (env : PacketEnvelope) : Bool :=
  fromBytes? env.toBytes == some env

/-- Packet envelope rejects an appended trailing byte instead of silently accepting it. -/
def trailingBytesRejected (env : PacketEnvelope) : Bool :=
  fromBytes? (snocByte env.toBytes 0) == none

/-- Packet envelope rejects a one-byte truncation of its encoded form. -/
def lastByteTruncationRejected (env : PacketEnvelope) : Bool :=
  if env.toBytes.size = 0 then
    false
  else
    fromBytes? (takeBytes env.toBytes (env.toBytes.size - 1)) == none

theorem matchesPacket_ofPacket (packet : Packet) :
    (ofPacket packet).matchesPacket packet = true := by
  simp [matchesPacket]

end PacketEnvelope

end VerifiedPQC
end Crypto
end HeytingLean
