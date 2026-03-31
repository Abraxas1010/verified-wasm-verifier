import Lean
import HeytingLean.Crypto.KEM.MLKEMStandardRuntime

namespace HeytingLean
namespace CLI

open Lean
open HeytingLean.Crypto.KEM.FIPS203

private def seedHex (byte : String) : String :=
  String.join (List.replicate 48 byte)

private def reportJson (label : String) (report : StandardRuntime.RoundtripReport) : Json :=
  Json.mkObj
    [ ("parameter_set", .str label)
    , ("ek_size", .num report.keyPair.ek.size)
    , ("dk_size", .num report.keyPair.dk.size)
    , ("ct_size", .num report.encapsulation.ciphertext.size)
    , ("ss_size", .num report.encapsulation.sharedSecret.size)
    , ("decap_ss_size", .num report.decapsulatedSecret.size)
    , ("keypair_checks", .bool report.keypairChecks)
    , ("ciphertext_check", .bool report.ciphertextCheck)
    , ("decapsulation_matches", .bool report.decapsulationMatches)
    ]

private def errorJson (label err : String) : Json :=
  Json.mkObj
    [ ("parameter_set", .str label)
    , ("error", .str err)
    ]

def main (_args : List String) : IO UInt32 := do
  let runs :=
    [ ("ML-KEM-512", mlkem512, seedHex "01", seedHex "11")
    , ("ML-KEM-768", mlkem768, seedHex "02", seedHex "12")
    , ("ML-KEM-1024", mlkem1024, seedHex "03", seedHex "13")
    ]
  let mut ok := true
  let mut results : Array Json := #[]
  for (label, p, keySeed, encSeed) in runs do
    match ← StandardRuntime.roundtrip p keySeed encSeed with
    | .ok report =>
        if !(report.keypairChecks && report.ciphertextCheck && report.decapsulationMatches) then
          ok := false
        results := results.push (reportJson label report)
    | .error err =>
        ok := false
        results := results.push (errorJson label err)
  IO.println (Json.arr results |>.compress)
  pure (if ok then 0 else 1)

end CLI
end HeytingLean

open HeytingLean CLI

def main (args : List String) : IO UInt32 :=
  CLI.main args
