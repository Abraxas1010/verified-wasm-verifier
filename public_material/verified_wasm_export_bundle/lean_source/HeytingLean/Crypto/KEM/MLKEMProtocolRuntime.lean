import HeytingLean.Crypto.KEM.MLKEMStandardRuntime
import HeytingLean.Crypto.DSA.MLDSAStandardRuntime
import HeytingLean.Crypto.VerifiedPQC.Protocol
import HeytingLean.Crypto.VerifiedPQC.CertificateRuntime
import HeytingLean.Crypto.VerifiedPQC.RuntimeBoundary
import HeytingLean.Crypto.VerifiedPQC.Serialization

namespace HeytingLean
namespace Crypto
namespace KEM

open VerifiedPQC

private def packetRoundtripOk (packet : Packet) : Bool :=
  let env := PacketEnvelope.ofPacket packet
  PacketEnvelope.fromBytes? env.toBytes == some env && env.matchesPacket packet

/-- Executable runtime bridge for the promoted ML-KEM protocol lane.

The packet, manifest, and certificate structures remain the same as the pure protocol layer; the
KEM and DSA seams are replaced here by the standardized FIPS 203 / FIPS 204 runtime boundaries,
while the carried-certificate layer remains an explicit local/carrying surface. -/
structure ProtocolRuntimeReport where
  keyPair : FIPS203.StandardRuntime.KeyPair
  senderPublicKey : DSA.PublicKey
  senderSecretKey : DSA.SecretKey
  packet : Packet
  verification : VerificationReport
  receivedPayload : ByteArray
  payloadMatches : Bool
  packetRoundtrip : Bool
  certificateVerified : Bool
  backendLabel : String

structure AuthenticatedPacket where
  packet : Packet
  certificateWitness : SignedCertificateWitness

structure AuthenticatedVerificationReport where
  base : VerificationReport
  certificateWitnessBaseOk : Bool
  certificateWitnessSignatureOk : Bool
  certificateWitnessBindsPacket : Bool
  passedChecks : Nat
  decision : Nat
  deriving DecidableEq, Repr

structure AuthenticatedProtocolRuntimeReport where
  keyPair : FIPS203.StandardRuntime.KeyPair
  senderPublicKey : DSA.PublicKey
  senderSecretKey : DSA.SecretKey
  authenticatedPacket : AuthenticatedPacket
  verification : AuthenticatedVerificationReport
  receivedPayload : ByteArray
  payloadMatches : Bool
  packetRoundtrip : Bool
  certificateVerified : Bool
  certificateWitnessVerified : Bool
  backendLabel : String

private def authenticatedPassedChecks (base : VerificationReport)
    (certificateWitnessOk certificateWitnessBindsPacket : Bool) : Nat :=
  base.passedChecks + boolToNat certificateWitnessOk + boolToNat certificateWitnessBindsPacket

def authenticatedDecision
    (baseDecision : Nat) (certificateWitnessOk certificateWitnessBindsPacket : Bool) : Nat :=
  if baseDecision = 1 && certificateWitnessOk && certificateWitnessBindsPacket then 1 else 0

theorem authenticatedDecision_eq_one_iff
    (baseDecision : Nat) (certificateWitnessOk certificateWitnessBindsPacket : Bool) :
    authenticatedDecision baseDecision certificateWitnessOk certificateWitnessBindsPacket = 1 ↔
      baseDecision = 1 ∧ certificateWitnessOk = true ∧ certificateWitnessBindsPacket = true := by
  by_cases hb : baseDecision = 1 <;> by_cases hc : certificateWitnessOk <;>
      by_cases hm : certificateWitnessBindsPacket <;>
      simp [authenticatedDecision, hb, hc, hm]

def AuthenticatedPacket.certificateMatchesPacket (authenticatedPacket : AuthenticatedPacket) : Bool :=
  decide
    (CertificateEnvelope.ofCertificate authenticatedPacket.certificateWitness.certificate =
      CertificateEnvelope.ofCertificate authenticatedPacket.packet.certificate)

/-- Runtime ML-KEM key generation promoted into the protocol carrier. -/
def runtimeKeygen (bundle : ParameterBundle) (seedHex : String := "") :
    IO (Except String (FIPS203.StandardRuntime.KeyPair × KEM.PublicKey × KEM.SecretKey)) := do
  match ← FIPS203.StandardRuntime.keygen bundle.kem seedHex with
  | .error e => pure (.error e)
  | .ok keyPair =>
      pure (.ok (keyPair, { bytes := keyPair.ek }, { bytes := keyPair.dk }))

/-- Send using the standardized ML-KEM and ML-DSA runtimes while preserving the packet envelope. -/
def sendWithStandardRuntime (bundle : ParameterBundle)
    (recipientPk : KEM.PublicKey)
    (payload : ByteArray)
    (certificate : CarriedCertificate)
    (encapSeedHex dsaSeedHex : String) :
    IO (Except String (DSA.PublicKey × DSA.SecretKey × Packet)) := do
  match ← FIPS203.StandardRuntime.encaps bundle.kem recipientPk.bytes encapSeedHex with
  | .error e => pure (.error e)
  | .ok enc =>
      let ciphertext : KEM.Ciphertext := { bytes := enc.ciphertext }
      let encryptedPayload := sealBody enc.sharedSecret payload
      let manifest := buildManifest ciphertext encryptedPayload certificate
      match ← DSA.FIPS204.StandardRuntime.keygenSignAttached bundle.dsa manifest.toBytes dsaSeedHex with
      | .error e => pure (.error e)
      | .ok signed =>
          let senderPk : DSA.PublicKey := { bytes := signed.publicKey }
          let senderSk : DSA.SecretKey := { bytes := signed.secretKey }
          pure (.ok
            (senderPk, senderSk,
              { kemCiphertext := ciphertext
                encryptedPayload := encryptedPayload
                manifest := manifest
                signedManifest := { bytes := signed.signedMessage }
                certificate := certificate }))

/-- Send with an additional native signed-certificate witness over the carried certificate. -/
def sendWithAuthenticatedCertificateRuntime (bundle : ParameterBundle)
    (recipientPk : KEM.PublicKey)
    (payload : ByteArray)
    (certificate : CarriedCertificate)
    (certSeedHex encapSeedHex dsaSeedHex : String) :
    IO (Except String (DSA.PublicKey × DSA.SecretKey × AuthenticatedPacket)) := do
  match ← signCertificateWithStandardRuntime bundle.dsa certificate certSeedHex with
  | .error e => pure (.error e)
  | .ok signedCertificate =>
      match ← sendWithStandardRuntime bundle recipientPk payload certificate encapSeedHex dsaSeedHex with
      | .error e => pure (.error e)
      | .ok (senderPk, senderSk, packet) =>
          pure (.ok
            (senderPk, senderSk,
              { packet := packet
                certificateWitness := signedCertificate.witness }))

/-- Verify a packet with runtime ML-KEM decapsulation and the existing signature/certificate checks. -/
def verifyPacketWithStandardRuntime (bundle : ParameterBundle)
    (senderPk : DSA.PublicKey)
    (recipientSk : KEM.SecretKey)
    (packet : Packet) : IO VerificationReport := do
  match ← FIPS203.StandardRuntime.decaps bundle.kem recipientSk.bytes packet.kemCiphertext.bytes with
  | .error _ =>
      let certificateOk := VerifiedPQC.verify packet.certificate
      let passed := countPassedChecks false certificateOk false false
      pure
        { decapOk := false
          certificateOk := certificateOk
          signatureOk := false
          manifestOk := false
          passedChecks := passed
          decision := acceptAllChecksFn passed }
  | .ok _ =>
      let certificateOk := VerifiedPQC.verify packet.certificate
      let signatureOk ←
        match ←
            DSA.FIPS204.StandardRuntime.openSignedMessage
              bundle.dsa senderPk.bytes packet.signedManifest.bytes packet.manifest.toBytes with
        | .ok () => pure true
        | .error _ => pure false
      let manifestOk :=
        packet.manifest =
          buildManifest packet.kemCiphertext packet.encryptedPayload packet.certificate
      let passed := countPassedChecks true certificateOk signatureOk manifestOk
      pure
        { decapOk := true
          certificateOk := certificateOk
          signatureOk := signatureOk
          manifestOk := manifestOk
          passedChecks := passed
          decision := acceptAllChecksFn passed }

/-- Verify a packet plus its native signed-certificate witness. -/
def verifyAuthenticatedPacketWithStandardRuntime (bundle : ParameterBundle)
    (senderPk : DSA.PublicKey)
    (recipientSk : KEM.SecretKey)
    (authenticatedPacket : AuthenticatedPacket) : IO AuthenticatedVerificationReport := do
  let base ← verifyPacketWithStandardRuntime bundle senderPk recipientSk authenticatedPacket.packet
  let certificateWitnessReport ←
    verifySignedCertificateWithStandardRuntime bundle.dsa authenticatedPacket.certificateWitness
  let certificateWitnessOk := certificateWitnessReport.decision = 1
  let certificateWitnessBindsPacket := authenticatedPacket.certificateMatchesPacket
  pure
    { base := base
      certificateWitnessBaseOk := certificateWitnessReport.baseCertificateOk
      certificateWitnessSignatureOk := certificateWitnessReport.signatureOk
      certificateWitnessBindsPacket := certificateWitnessBindsPacket
      passedChecks :=
        authenticatedPassedChecks base certificateWitnessOk certificateWitnessBindsPacket
      decision :=
        authenticatedDecision base.decision certificateWitnessOk certificateWitnessBindsPacket }

/-- Receive using the standardized ML-KEM runtime while preserving the existing acceptance kernel. -/
def receiveWithStandardRuntime (bundle : ParameterBundle)
    (senderPk : DSA.PublicKey)
    (recipientSk : KEM.SecretKey)
    (packet : Packet) : IO (Except ReceiveError ByteArray) := do
  let report ← verifyPacketWithStandardRuntime bundle senderPk recipientSk packet
  match ← FIPS203.StandardRuntime.decaps bundle.kem recipientSk.bytes packet.kemCiphertext.bytes with
  | .error _ => pure (.error .decapsulationFailed)
  | .ok ss =>
      if report.decision = 1 then
        pure (.ok (openBody ss packet.encryptedPayload))
      else
        pure (.error .verificationRejected)

/-- Receive succeeds only when both the base packet and the signed-certificate witness verify. -/
def receiveAuthenticatedWithStandardRuntime (bundle : ParameterBundle)
    (senderPk : DSA.PublicKey)
    (recipientSk : KEM.SecretKey)
    (authenticatedPacket : AuthenticatedPacket) : IO (Except ReceiveError ByteArray) := do
  let report ← verifyAuthenticatedPacketWithStandardRuntime bundle senderPk recipientSk authenticatedPacket
  match ← FIPS203.StandardRuntime.decaps bundle.kem recipientSk.bytes authenticatedPacket.packet.kemCiphertext.bytes with
  | .error _ => pure (.error .decapsulationFailed)
  | .ok ss =>
      if report.decision = 1 then
        pure (.ok (openBody ss authenticatedPacket.packet.encryptedPayload))
      else
        pure (.error .verificationRejected)

/-- End-to-end runtime roundtrip for the promoted protocol lane. -/
def runtimeRoundtrip (bundle : ParameterBundle)
    (keySeedHex encapSeedHex dsaSeedHex : String)
    (payload : ByteArray)
    (certificate : CarriedCertificate) :
    IO (Except String ProtocolRuntimeReport) := do
  match ← runtimeKeygen bundle keySeedHex with
  | .error e => pure (.error e)
  | .ok (keyPair, recipientPk, recipientSk) =>
      match ← sendWithStandardRuntime bundle recipientPk payload certificate encapSeedHex dsaSeedHex with
      | .error e => pure (.error e)
      | .ok (senderPk, senderSk, packet) =>
          let verification ← verifyPacketWithStandardRuntime bundle senderPk recipientSk packet
          match ← receiveWithStandardRuntime bundle senderPk recipientSk packet with
          | .error err => pure (.error s!"receive failed: {reprStr err}")
          | .ok receivedPayload =>
              pure (.ok
                { keyPair := keyPair
                  senderPublicKey := senderPk
                  senderSecretKey := senderSk
                  packet := packet
                  verification := verification
                  receivedPayload := receivedPayload
                  payloadMatches := receivedPayload == payload
                  packetRoundtrip := packetRoundtripOk packet
                  certificateVerified := VerifiedPQC.verify packet.certificate
                  backendLabel :=
                    s!"{(VerifiedPQC.standardRuntimeBundle bundle).kem.scheme}+{(VerifiedPQC.standardRuntimeBundle bundle).dsa.scheme}" })

/-- End-to-end authenticated runtime roundtrip for the strengthened protocol lane. -/
def runtimeAuthenticatedRoundtrip (bundle : ParameterBundle)
    (keySeedHex certSeedHex encapSeedHex dsaSeedHex : String)
    (payload : ByteArray)
    (certificate : CarriedCertificate) :
    IO (Except String AuthenticatedProtocolRuntimeReport) := do
  match ← runtimeKeygen bundle keySeedHex with
  | .error e => pure (.error e)
  | .ok (keyPair, recipientPk, recipientSk) =>
      match ←
          sendWithAuthenticatedCertificateRuntime
            bundle recipientPk payload certificate certSeedHex encapSeedHex dsaSeedHex with
      | .error e => pure (.error e)
      | .ok (senderPk, senderSk, authenticatedPacket) =>
          let verification ←
            verifyAuthenticatedPacketWithStandardRuntime bundle senderPk recipientSk authenticatedPacket
          match ← receiveAuthenticatedWithStandardRuntime bundle senderPk recipientSk authenticatedPacket with
          | .error err => pure (.error s!"authenticated receive failed: {reprStr err}")
          | .ok receivedPayload =>
              pure (.ok
                { keyPair := keyPair
                  senderPublicKey := senderPk
                  senderSecretKey := senderSk
                  authenticatedPacket := authenticatedPacket
                  verification := verification
                  receivedPayload := receivedPayload
                  payloadMatches := receivedPayload == payload
                  packetRoundtrip := packetRoundtripOk authenticatedPacket.packet
                  certificateVerified := VerifiedPQC.verify authenticatedPacket.packet.certificate
                  certificateWitnessVerified :=
                    verification.certificateWitnessBaseOk &&
                    verification.certificateWitnessSignatureOk &&
                    verification.certificateWitnessBindsPacket
                  backendLabel :=
                    s!"{(VerifiedPQC.standardRuntimeBundle bundle).kem.scheme}+{(VerifiedPQC.standardRuntimeBundle bundle).dsa.scheme}" })

end KEM
end Crypto
end HeytingLean
