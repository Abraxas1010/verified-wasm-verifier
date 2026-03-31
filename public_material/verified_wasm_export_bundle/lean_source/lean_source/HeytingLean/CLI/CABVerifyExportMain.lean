import Lean.Data.Json
import HeytingLean.Meta.LeanTT0.ExportCAB
import HeytingLean.CLI.Args

/-!
# `cab_verify_export` - Verify CAB Certificates for Lens Exports

Verifies that generated C/Python artifacts match their CAB certificate.

## Usage

```bash
lake exe cab_verify_export path/to/certificate.json
```

## Verification Steps

1. Parse the certificate.json
2. Read each artifact file listed in the certificate
3. Compute SHA-256 hash of each file
4. Compare against expected hashes in certificate
5. Recompute Merkle root and compare

## Exit Codes

- 0: All artifacts verified successfully
- 1: Verification failed (hash mismatch or missing file)
- 2: Certificate parse error
- 3: Usage error
-/

namespace HeytingLean
namespace CLI
namespace CABVerifyExport

open Lean
open HeytingLean.Meta.LeanTT0.ExportCAB

private def usage : String :=
  String.intercalate "\n"
    [ "cab_verify_export - Verify CAB certificates for lens exports"
    , ""
    , "Usage:"
    , "  lake exe cab_verify_export <certificate.json>"
    , ""
    , "Options:"
    , "  --verbose    Show detailed verification output"
    , "  --json       Output results as JSON"
    , "  --help       Show this message"
    , ""
    , "Exit codes:"
    , "  0 - Verification successful"
    , "  1 - Verification failed"
    , "  2 - Certificate parse error"
    , "  3 - Usage error"
    ]

structure Config where
  certPath : Option String := none
  verbose : Bool := false
  jsonOutput : Bool := false
deriving Repr

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) :=
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--verbose" :: rest => parseArgs rest { cfg with verbose := true }
  | "--json" :: rest => parseArgs rest { cfg with jsonOutput := true }
  | x :: rest =>
    if x.startsWith "-" then
      throw <| IO.userError s!"unknown flag: {x} (try --help)"
    else if cfg.certPath.isNone then
      parseArgs rest { cfg with certPath := some x }
    else
      throw <| IO.userError s!"unexpected argument: {x}"

/-- Parse a JSON file -/
private def parseJsonFile (path : System.FilePath) : IO Json := do
  let content ← IO.FS.readFile path
  match Json.parse content with
  | Except.ok json => pure json
  | Except.error msg => throw <| IO.userError s!"JSON parse error: {msg}"

/-- Get the directory containing the certificate -/
private def certDir (certPath : System.FilePath) : System.FilePath :=
  certPath.parent.getD (System.FilePath.mk ".")

/-- Verify all artifacts in a certificate -/
private def verifyAllArtifacts (cert : Json) (baseDir : System.FilePath) (verbose : Bool) : IO VerificationResult := do
  let some artifacts := parseArtifactHashes cert
    | return { success := false, merkleRoot := "", artifactCount := 0, failedArtifacts := ["certificate has no artifacts"] }

  let some expectedRoot := parseMerkleRoot cert
    | return { success := false, merkleRoot := "", artifactCount := 0, failedArtifacts := ["certificate has no merkle_root"] }

  let mut failed : List String := []
  let mut contents : List (String × String) := []

  for (name, expectedHash) in artifacts do
    let filePath := baseDir / name
    if verbose then
      IO.println s!"Verifying {name}..."
    try
      let content ← IO.FS.readFile filePath
      let computedHash := hexEncode (hashString content)
      if computedHash == expectedHash then
        if verbose then
          IO.println s!"  ✓ {name}: hash matches"
        contents := (name, content) :: contents
      else
        if verbose then
          IO.println s!"  ✗ {name}: hash mismatch"
          IO.println s!"    expected: {expectedHash}"
          IO.println s!"    computed: {computedHash}"
        failed := name :: failed
    catch _ =>
      if verbose then
        IO.println s!"  ✗ {name}: file not found"
      failed := s!"{name} (not found)" :: failed

  -- Verify Merkle root
  let computedRoot := if contents.isEmpty then "" else recomputeMerkleRoot contents.reverse
  if computedRoot != expectedRoot && failed.isEmpty then
    if verbose then
      IO.println s!"Merkle root mismatch!"
      IO.println s!"  expected: {expectedRoot}"
      IO.println s!"  computed: {computedRoot}"
    failed := "merkle_root" :: failed

  return {
    success := failed.isEmpty
    merkleRoot := computedRoot
    artifactCount := artifacts.length
    failedArtifacts := failed.reverse
  }

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  if args.isEmpty then
    IO.println usage
    return (0 : UInt32)
  try
    let (cfg, showHelp) ← parseArgs args
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    let some certPath := cfg.certPath
      | do
        IO.eprintln "Error: certificate path required"
        IO.eprintln ""
        IO.eprintln usage
        return (3 : UInt32)

    let certFilePath := System.FilePath.mk certPath

    -- Parse certificate
    let cert ← parseJsonFile certFilePath

    -- Get lens info
    let lensId := cert.getObjValAs? String "lens_id" |>.toOption.getD "unknown"
    let version := cert.getObjValAs? String "version" |>.toOption.getD "unknown"

    if cfg.verbose then
      IO.println s!"=== CAB Certificate Verification ==="
      IO.println s!"Certificate: {certPath}"
      IO.println s!"Lens: {lensId}"
      IO.println s!"Version: {version}"
      IO.println ""

    -- Verify artifacts
    let result ← verifyAllArtifacts cert (certDir certFilePath) cfg.verbose

    if cfg.jsonOutput then
      IO.println (Json.pretty (toVerificationJson result))
    else
      if result.success then
        IO.println s!"✓ Verification PASSED"
        IO.println s!"  Lens: {lensId}"
        IO.println s!"  Artifacts: {result.artifactCount}"
        IO.println s!"  Merkle root: {result.merkleRoot}"
      else
        IO.println s!"✗ Verification FAILED"
        IO.println s!"  Lens: {lensId}"
        IO.println s!"  Failed artifacts:"
        for f in result.failedArtifacts do
          IO.println s!"    - {f}"

    return if result.success then (0 : UInt32) else (1 : UInt32)

  catch e =>
    IO.eprintln s!"Error: {e}"
    return (2 : UInt32)

end CABVerifyExport
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.CABVerifyExport.main args
