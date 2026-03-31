import Lean
import HeytingLean.Crypto.KEM.MLKEMProtocolRuntime
import HeytingLean.Crypto.VerifiedPQC.Programs

namespace HeytingLean
namespace CLI

open Lean
open HeytingLean.Crypto

private def seedHex (byte : String) : String :=
  String.join (List.replicate 48 byte)

private def reportJson (kemName dsaName : String) (report : KEM.ProtocolRuntimeReport) : Json :=
  Json.mkObj
    [ ("kem_parameter_set", .str kemName)
    , ("dsa_parameter_set", .str dsaName)
    , ("backend_label", .str report.backendLabel)
    , ("ek_size", .num report.keyPair.ek.size)
    , ("dk_size", .num report.keyPair.dk.size)
    , ("ct_size", .num report.packet.kemCiphertext.bytes.size)
    , ("payload_size", .num report.receivedPayload.size)
    , ("packet_roundtrip", .bool report.packetRoundtrip)
    , ("certificate_verified", .bool report.certificateVerified)
    , ("decap_ok", .bool report.verification.decapOk)
    , ("signature_ok", .bool report.verification.signatureOk)
    , ("manifest_ok", .bool report.verification.manifestOk)
    , ("payload_matches", .bool report.payloadMatches)
    , ("decision", .num report.verification.decision)
    ]

private def authenticatedReportJson
    (kemName dsaName : String) (report : KEM.AuthenticatedProtocolRuntimeReport) : Json :=
  Json.mkObj
    [ ("kem_parameter_set", .str kemName)
    , ("dsa_parameter_set", .str dsaName)
    , ("backend_label", .str report.backendLabel)
    , ("ek_size", .num report.keyPair.ek.size)
    , ("dk_size", .num report.keyPair.dk.size)
    , ("ct_size", .num report.authenticatedPacket.packet.kemCiphertext.bytes.size)
    , ("payload_size", .num report.receivedPayload.size)
    , ("packet_roundtrip", .bool report.packetRoundtrip)
    , ("certificate_verified", .bool report.certificateVerified)
    , ("certificate_witness_verified", .bool report.certificateWitnessVerified)
    , ("decap_ok", .bool report.verification.base.decapOk)
    , ("signature_ok", .bool report.verification.base.signatureOk)
    , ("manifest_ok", .bool report.verification.base.manifestOk)
    , ("certificate_witness_signature_ok", .bool report.verification.certificateWitnessSignatureOk)
    , ("certificate_witness_binds_packet", .bool report.verification.certificateWitnessBindsPacket)
    , ("payload_matches", .bool report.payloadMatches)
    , ("decision", .num report.verification.decision)
    ]

private def errorJson (kemName dsaName err : String) : Json :=
  Json.mkObj
    [ ("kem_parameter_set", .str kemName)
    , ("dsa_parameter_set", .str dsaName)
    , ("error", .str err)
    ]

def main (_args : List String) : IO UInt32 := do
  let certificate :=
    VerifiedPQC.acceptAllChecksCertificate ("mlkem-protocol-runtime-proof" : String).toUTF8
  let runs :=
    [ ("ML-KEM-512", KEM.FIPS203.mlkem512, "ML-DSA-44", DSA.FIPS204.mldsa44, seedHex "01", seedHex "11", seedHex "21")
    , ("ML-KEM-768", KEM.FIPS203.mlkem768, "ML-DSA-65", DSA.FIPS204.mldsa65, seedHex "02", seedHex "12", seedHex "22")
    , ("ML-KEM-1024", KEM.FIPS203.mlkem1024, "ML-DSA-87", DSA.FIPS204.mldsa87, seedHex "03", seedHex "13", seedHex "23")
    ]
  let mut ok := true
  let mut results : Array Json := #[]
  let mut authenticatedResults : Array Json := #[]
  for (kemName, kem, dsaName, dsa, keySeed, encSeed, dsaSeed) in runs do
    let bundle : VerifiedPQC.ParameterBundle := { kem := kem, dsa := dsa }
    let payload := s!"runtime-protocol-payload:{kemName}" |>.toUTF8
    match ← KEM.runtimeRoundtrip bundle keySeed encSeed dsaSeed payload certificate with
    | .ok report =>
        if !(report.packetRoundtrip && report.certificateVerified &&
            report.verification.decapOk && report.verification.signatureOk &&
            report.verification.manifestOk && report.payloadMatches &&
            report.verification.decision = 1) then
          ok := false
        results := results.push (reportJson kemName dsaName report)
    | .error err =>
        ok := false
        results := results.push (errorJson kemName dsaName err)
    match ← KEM.runtimeAuthenticatedRoundtrip bundle keySeed (seedHex s!"9{kem.k}") encSeed dsaSeed payload certificate with
    | .ok report =>
        if !(report.packetRoundtrip && report.certificateVerified &&
            report.certificateWitnessVerified && report.verification.base.decapOk &&
            report.verification.base.signatureOk && report.verification.base.manifestOk &&
            report.verification.certificateWitnessSignatureOk &&
            report.verification.certificateWitnessBindsPacket &&
            report.payloadMatches && report.verification.decision = 1) then
          ok := false
        authenticatedResults := authenticatedResults.push (authenticatedReportJson kemName dsaName report)
    | .error err =>
        ok := false
        authenticatedResults := authenticatedResults.push (errorJson kemName dsaName err)
  IO.println
    (Json.mkObj
      [ ("standard_roundtrip", Json.arr results)
      , ("authenticated_roundtrip", Json.arr authenticatedResults)
      ] |>.compress)
  pure (if ok then 0 else 1)

end CLI
end HeytingLean

open HeytingLean CLI

def main (args : List String) : IO UInt32 :=
  CLI.main args
