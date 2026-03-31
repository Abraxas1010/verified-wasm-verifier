import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Crypto.VerifiedPQC.Programs
import HeytingLean.Meta.LeanTT0.ExportCAB

namespace HeytingLean.CLI.VerifiedPQCExport

open Lean
open HeytingLean.Crypto.VerifiedPQC
open HeytingLean.Meta.LeanTT0.ExportCAB

structure Config where
  outDir : String := "artifacts/crypto/verified_pqc_export"
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "verified_pqc_export - Export the carried verifier kernel"
    , ""
    , "Usage:"
    , "  lake exe verified_pqc_export --out <dir>"
    , ""
    , "Output:"
    , "  kernel.c"
    , "  kernel.h"
    , "  driver.c"
    , "  expected.txt"
    , "  provenance.json"
    , "  certificate.json"
    ]

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) :=
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--out" :: dir :: rest => parseArgs rest { cfg with outDir := dir }
  | x :: _ => throw <| IO.userError s!"unknown flag: {x} (try --help)"

private def resolveOutDir (dir : String) : IO System.FilePath := do
  if dir.startsWith "/" then
    return System.FilePath.mk dir
  let cwd ← IO.currentDir
  let base :=
    if cwd.fileName == some "lean" then cwd.parent.getD cwd else cwd
  return base / dir

private def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  let some parent := path.parent
    | throw <| IO.userError s!"could not compute parent directory for {path}"
  IO.FS.createDirAll parent
  IO.FS.writeFile path contents

private def expectedOutput : String :=
  String.intercalate "\n"
    [ "0:0"
    , "1:0"
    , "2:0"
    , "3:0"
    , "4:1"
    ]

private def driverSource : String :=
  String.intercalate "\n"
    [ "#include <stdint.h>"
    , "#include <stdio.h>"
    , "#include \"kernel.h\""
    , ""
    , "int main(void) {"
    , "  for (uint64_t i = 0; i <= 4; ++i) {"
    , "    printf(\"%llu:%llu\\n\","
    , "      (unsigned long long)i,"
    , "      (unsigned long long)verified_pqc_accept_all_checks(i));"
    , "  }"
    , "  return 0;"
    , "}"
    ]

private def headerSource : String :=
  String.intercalate "\n"
    [ "#pragma once"
    , "#include <stdint.h>"
    , "uint64_t verified_pqc_accept_all_checks(uint64_t passed_checks);"
    ]

private def provenanceJson : Json :=
  Json.mkObj
    [ ("program_id", Json.str acceptAllChecksProgram.artifact.header.name)
    , ("lean_modules", Json.arr #[Json.str "HeytingLean.Crypto.VerifiedPQC.Programs",
                                  Json.str "HeytingLean.LeanCP.Examples.VerifiedPQCVerifier"])
    , ("theorems", Json.arr #[Json.str "verify_acceptAllChecksCertificate",
                             Json.str "verifiedPQCVerifier_verified"])
    , ("description", Json.str "Exported carried verifier kernel for the VerifiedPQC packet path")
    ]

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  try
    let (cfg, showHelp) ← parseArgs args
    if showHelp then
      IO.println usage
      return (0 : UInt32)
    let outDir ← resolveOutDir cfg.outDir
    let kernelSource := acceptAllChecksProgram.artifact.cCode
    let cert :=
      generateCertificateV2
        "verified_pqc_accept_all_checks"
        [ { name := "kernel.h", content := headerSource }
        , { name := "kernel.c", content := kernelSource }
        , { name := "driver.c", content := driverSource }
        , { name := "expected.txt", content := expectedOutput }
        , { name := "provenance.json", content := Json.pretty provenanceJson }
        ]
        [ "HeytingLean.Crypto.VerifiedPQC.verify_acceptAllChecksCertificate"
        , "HeytingLean.LeanCP.Examples.verifiedPQCVerifier_verified"
        ]
        [ "HeytingLean.Crypto.VerifiedPQC.Programs"
        , "HeytingLean.LeanCP.Examples.VerifiedPQCVerifier"
        ]
        VerificationTier.gold
        (some {
          method := "LeanCP"
          gpuAccelerated := false
          latentDim := 0
          bounds := none
          compositional := true
          verificationTimeSeconds := 0.0
        })
        none
        "VerifiedPQC carried verifier kernel export"

    writeFile (outDir / "kernel.h") headerSource
    writeFile (outDir / "kernel.c") kernelSource
    writeFile (outDir / "driver.c") driverSource
    writeFile (outDir / "expected.txt") expectedOutput
    writeFile (outDir / "provenance.json") (Json.pretty provenanceJson)
    writeFile (outDir / "certificate.json") (Json.pretty cert)
    IO.println s!"[verified_pqc_export] wrote {outDir}"
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"Error: {e}"
    return (1 : UInt32)

end HeytingLean.CLI.VerifiedPQCExport

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.VerifiedPQCExport.main args
