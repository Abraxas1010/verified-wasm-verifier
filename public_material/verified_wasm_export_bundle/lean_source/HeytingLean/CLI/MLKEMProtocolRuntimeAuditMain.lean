import Lean
import HeytingLean.Crypto.KEM.MLKEMProtocolRuntime
import HeytingLean.Crypto.VerifiedPQC.Programs

namespace HeytingLean
namespace CLI

open Lean
open HeytingLean.Crypto
open HeytingLean.Crypto.VerifiedPQC

private def seedHex (byte : String) : String :=
  String.join (List.replicate 48 byte)

private def flipFirstByte (bytes : ByteArray) : ByteArray :=
  if bytes.size > 0 then
    ByteArray.mk (bytes.data.set! 0 (bytes.data[0]! ^^^ UInt8.ofNat 1))
  else
    bytes

private def snocByte (bytes : ByteArray) (b : UInt8) : ByteArray :=
  ByteArray.mk (bytes.data.push b)

private def dropLastByte (bytes : ByteArray) : ByteArray :=
  if bytes.size = 0 then
    bytes
  else
    ByteArray.mk (bytes.data.extract 0 (bytes.size - 1))

private def tamperSignedManifest (packet : Packet) : Packet :=
  { packet with signedManifest := { bytes := flipFirstByte packet.signedManifest.bytes } }

private def tamperEncryptedPayload (packet : Packet) : Packet :=
  { packet with encryptedPayload := flipFirstByte packet.encryptedPayload }

private def tamperCertificateProof (packet : Packet) : Packet :=
  { packet with certificate := { packet.certificate with proofBytes := flipFirstByte packet.certificate.proofBytes } }

private def boolField (name : String) (b : Bool) : String × Json :=
  (name, .bool b)

private def natField (name : String) (n : Nat) : String × Json :=
  (name, .num n)

private def stringField (name value : String) : String × Json :=
  (name, .str value)

private def expectRejected (result : Except ReceiveError ByteArray) : Bool :=
  match result with
  | .error .verificationRejected => true
  | _ => false

private def containsSubstr (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

private def reportScenario (name : String) (report : VerificationReport) (receiveRejected : Bool) : Json :=
  Json.mkObj
    [ stringField "scenario" name
    , boolField "decap_ok" report.decapOk
    , boolField "certificate_ok" report.certificateOk
    , boolField "signature_ok" report.signatureOk
    , boolField "manifest_ok" report.manifestOk
    , natField "decision" report.decision
    , boolField "receive_rejected" receiveRejected
    ]

private def reportAuthenticatedScenario
    (name : String) (report : KEM.AuthenticatedVerificationReport) (receiveRejected : Bool) : Json :=
  Json.mkObj
    [ stringField "scenario" name
    , boolField "decap_ok" report.base.decapOk
    , boolField "certificate_ok" report.base.certificateOk
    , boolField "signature_ok" report.base.signatureOk
    , boolField "manifest_ok" report.base.manifestOk
    , boolField "certificate_witness_base_ok" report.certificateWitnessBaseOk
    , boolField "certificate_witness_signature_ok" report.certificateWitnessSignatureOk
    , boolField "certificate_witness_binds_packet" report.certificateWitnessBindsPacket
    , natField "decision" report.decision
    , boolField "receive_rejected" receiveRejected
    ]

private def errorScenario (name err : String) : Json :=
  Json.mkObj [stringField "scenario" name, stringField "error" err]

def main (_args : List String) : IO UInt32 := do
  let bundle : ParameterBundle :=
    { kem := KEM.FIPS203.mlkem768
      dsa := DSA.FIPS204.mldsa65 }
  let mismatchBundle : ParameterBundle :=
    { kem := KEM.FIPS203.mlkem1024
      dsa := DSA.FIPS204.mldsa87 }
  let certificate :=
    VerifiedPQC.acceptAllChecksCertificate ("mlkem-protocol-runtime-audit" : String).toUTF8
  let alternateCertificate :=
    VerifiedPQC.acceptAllChecksCertificate ("mlkem-protocol-runtime-audit-alt" : String).toUTF8
  let payload := ("runtime-protocol-audit-payload" : String).toUTF8
  let mut ok := true
  let mut results : Array Json := #[]

  match ← KEM.runtimeKeygen bundle (seedHex "31") with
  | .error err =>
      IO.println ((Json.arr #[errorScenario "keygen" err]).compress)
      pure 1
  | .ok (_keyPair, recipientPk, recipientSk) =>
      match ← KEM.sendWithStandardRuntime bundle recipientPk payload certificate (seedHex "41") (seedHex "51") with
      | .error err =>
          IO.println ((Json.arr #[errorScenario "send" err]).compress)
          pure 1
      | .ok (senderPk, _senderSk, packet) =>
          let scenarios :=
            [ ("signed_manifest_tamper", tamperSignedManifest packet)
            , ("encrypted_payload_tamper", tamperEncryptedPayload packet)
            , ("certificate_proof_tamper", tamperCertificateProof packet)
            ]
          for (name, tampered) in scenarios do
            let report ← KEM.verifyPacketWithStandardRuntime bundle senderPk recipientSk tampered
            let receiveResult ← KEM.receiveWithStandardRuntime bundle senderPk recipientSk tampered
            let scenarioJson := reportScenario name report (expectRejected receiveResult)
            let passed :=
              report.decision = 0 && expectRejected receiveResult &&
              match name with
              | "signed_manifest_tamper" => !report.signatureOk && report.manifestOk
              | "encrypted_payload_tamper" => report.signatureOk && !report.manifestOk
              | _ => !report.certificateOk && report.signatureOk && report.manifestOk
            if !passed then
              ok := false
            results := results.push scenarioJson

          match ←
              DSA.FIPS204.StandardRuntime.openSignedMessage bundle.dsa
                (dropLastByte senderPk.bytes) packet.signedManifest.bytes packet.manifest.toBytes with
          | .ok () =>
              ok := false
              results := results.push (errorScenario "truncated_public_key_rejection" "unexpected success")
          | .error err =>
              let passed := containsSubstr err "size check"
              if !passed then
                ok := false
              results := results.push (Json.mkObj
                [ stringField "scenario" "truncated_public_key_rejection"
                , boolField "size_check_rejected" passed
                , stringField "detail" err
                ])

          match ←
              DSA.FIPS204.StandardRuntime.openSignedMessage bundle.dsa
                senderPk.bytes (dropLastByte packet.signedManifest.bytes) packet.manifest.toBytes with
          | .ok () =>
              ok := false
              results := results.push (errorScenario "truncated_signed_message_rejection" "unexpected success")
          | .error err =>
              let passed := containsSubstr err "size check"
              if !passed then
                ok := false
              results := results.push (Json.mkObj
                [ stringField "scenario" "truncated_signed_message_rejection"
                , boolField "size_check_rejected" passed
                , stringField "detail" err
                ])

          match ←
              KEM.FIPS203.StandardRuntime.decaps
                bundle.kem (dropLastByte recipientSk.bytes) packet.kemCiphertext.bytes with
          | .ok _ =>
              ok := false
              results := results.push (errorScenario "truncated_decapsulation_key_rejection" "unexpected success")
          | .error err =>
              let passed := containsSubstr err "decapsulation key failed local check"
              if !passed then
                ok := false
              results := results.push (Json.mkObj
                [ stringField "scenario" "truncated_decapsulation_key_rejection"
                , boolField "size_check_rejected" passed
                , stringField "detail" err
                ])

          match ←
              KEM.FIPS203.StandardRuntime.decaps
                bundle.kem recipientSk.bytes (dropLastByte packet.kemCiphertext.bytes) with
          | .ok _ =>
              ok := false
              results := results.push (errorScenario "truncated_ciphertext_rejection" "unexpected success")
          | .error err =>
              let passed := containsSubstr err "ciphertext failed local size check"
              if !passed then
                ok := false
              results := results.push (Json.mkObj
                [ stringField "scenario" "truncated_ciphertext_rejection"
                , boolField "size_check_rejected" passed
                , stringField "detail" err
                ])

          match ←
              KEM.FIPS203.StandardRuntime.decaps
                bundle.kem recipientSk.bytes (snocByte packet.kemCiphertext.bytes 0) with
          | .ok _ =>
              ok := false
              results := results.push (errorScenario "oversized_ciphertext_rejection" "unexpected success")
          | .error err =>
              let passed := containsSubstr err "ciphertext failed local size check"
              if !passed then
                ok := false
              results := results.push (Json.mkObj
                [ stringField "scenario" "oversized_ciphertext_rejection"
                , boolField "size_check_rejected" passed
                , stringField "detail" err
                ])

          let mismatchReport ←
            KEM.verifyPacketWithStandardRuntime mismatchBundle senderPk recipientSk packet
          let mismatchReceive ←
            KEM.receiveWithStandardRuntime mismatchBundle senderPk recipientSk packet
          let mismatchRejected :=
            match mismatchReceive with
            | .error .decapsulationFailed => true
            | .error .verificationRejected => true
            | .ok _ => false
          let mismatchPassed := mismatchReport.decision = 0 && mismatchRejected && !mismatchReport.decapOk
          if !mismatchPassed then
            ok := false
          results := results.push (Json.mkObj
            [ stringField "scenario" "parameter_mismatch_rejection"
            , boolField "decap_ok" mismatchReport.decapOk
            , natField "decision" mismatchReport.decision
            , boolField "receive_rejected" mismatchRejected
            ])

          match ←
              KEM.sendWithAuthenticatedCertificateRuntime
                bundle recipientPk payload certificate (seedHex "61") (seedHex "41") (seedHex "51") with
          | .error err =>
              ok := false
              results := results.push (errorScenario "authenticated_send" err)
          | .ok (authSenderPk, _authSenderSk, authenticatedPacket) =>
              let authenticatedOkReport ←
                KEM.verifyAuthenticatedPacketWithStandardRuntime
                  bundle authSenderPk recipientSk authenticatedPacket
              let authenticatedOkReceive ←
                KEM.receiveAuthenticatedWithStandardRuntime
                  bundle authSenderPk recipientSk authenticatedPacket
              let authenticatedOkPassed :=
                authenticatedOkReport.decision = 1 &&
                match authenticatedOkReceive with
                | .ok recovered => recovered = payload
                | .error _ => false
              if !authenticatedOkPassed then
                ok := false
              results := results.push (Json.mkObj
                [ stringField "scenario" "authenticated_roundtrip"
                , natField "decision" authenticatedOkReport.decision
                , boolField "certificate_witness_signature_ok" authenticatedOkReport.certificateWitnessSignatureOk
                , boolField "certificate_witness_binds_packet" authenticatedOkReport.certificateWitnessBindsPacket
                , boolField "payload_recovered" authenticatedOkPassed
                ])

              let tamperedAuthenticatedSignature : KEM.AuthenticatedPacket :=
                { authenticatedPacket with
                    certificateWitness :=
                      { authenticatedPacket.certificateWitness with
                          signature := flipFirstByte authenticatedPacket.certificateWitness.signature } }
              let tamperedSignatureReport ←
                KEM.verifyAuthenticatedPacketWithStandardRuntime
                  bundle authSenderPk recipientSk tamperedAuthenticatedSignature
              let tamperedSignatureReceive ←
                KEM.receiveAuthenticatedWithStandardRuntime
                  bundle authSenderPk recipientSk tamperedAuthenticatedSignature
              let tamperedSignatureRejected := expectRejected tamperedSignatureReceive
              let tamperedSignaturePassed :=
                tamperedSignatureReport.decision = 0 &&
                tamperedSignatureRejected &&
                !tamperedSignatureReport.certificateWitnessSignatureOk &&
                tamperedSignatureReport.certificateWitnessBindsPacket
              if !tamperedSignaturePassed then
                ok := false
              results := results.push
                (reportAuthenticatedScenario
                  "authenticated_certificate_signature_tamper"
                  tamperedSignatureReport tamperedSignatureRejected)

              match ←
                  VerifiedPQC.signCertificateWithStandardRuntime
                    bundle.dsa alternateCertificate (seedHex "62") with
              | .error err =>
                  ok := false
                  results := results.push (errorScenario "alternate_certificate_sign" err)
              | .ok alternateWitness =>
                  let mismatchedAuthenticatedPacket : KEM.AuthenticatedPacket :=
                    { packet := authenticatedPacket.packet
                      certificateWitness := alternateWitness.witness }
                  let mismatchedWitnessReport ←
                    KEM.verifyAuthenticatedPacketWithStandardRuntime
                      bundle authSenderPk recipientSk mismatchedAuthenticatedPacket
                  let mismatchedWitnessReceive ←
                    KEM.receiveAuthenticatedWithStandardRuntime
                      bundle authSenderPk recipientSk mismatchedAuthenticatedPacket
                  let mismatchedWitnessRejected := expectRejected mismatchedWitnessReceive
                  let mismatchedWitnessPassed :=
                    mismatchedWitnessReport.decision = 0 &&
                    mismatchedWitnessRejected &&
                    mismatchedWitnessReport.certificateWitnessSignatureOk &&
                    !mismatchedWitnessReport.certificateWitnessBindsPacket
                  if !mismatchedWitnessPassed then
                    ok := false
                  results := results.push
                    (reportAuthenticatedScenario
                      "authenticated_certificate_binding_tamper"
                      mismatchedWitnessReport mismatchedWitnessRejected)

          IO.println ((Json.arr results).compress)
          pure (if ok then 0 else 1)

end CLI
end HeytingLean

open HeytingLean CLI

def main (args : List String) : IO UInt32 :=
  CLI.main args
