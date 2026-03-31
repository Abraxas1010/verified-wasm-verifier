import Lean
import HeytingLean.Exec.Core
import HeytingLean.Exec.Registry
import HeytingLean.Exec.Manifest
import HeytingLean.Theorems.Core
import HeytingLean.Theorems.Cert

open Lean
open System
open HeytingLean.Exec
open HeytingLean.Exec.Manifest
open HeytingLean.Theorems

namespace HeytingLean
namespace CLI
namespace ProcMetadata

private def gitRev? : IO String := do
  try
    let result ←
      IO.Process.output
        { cmd := "git", args := #["rev-parse", "HEAD"], cwd := ".." }
    if result.exitCode = 0 then
      pure result.stdout.trim
    else
      pure "unknown"
  catch _ =>
    pure "unknown"

private def summaryFor (spec : ProcSpec) : IO CertifiedThmSummary := do
  let some block := findThmByName spec.specThm.name
    | throw <| IO.userError s!"unknown theorem in proc spec: {spec.specThm.name}"
  let cert ← getThmCert block
  pure <| HeytingLean.Theorems.toSummary { block, cert }

private def entryFor (p : Proc) : IO ProcManifestEntry := do
  let summary ← summaryFor p.spec
  let some block := findThmByName p.spec.specThm.name
    | throw <| IO.userError s!"unknown theorem in proc spec: {p.spec.specThm.name}"
  let tags := block.tags.namespaceHint ++ block.tags.lensHint
  pure {
    id := p.id
    arity := arityToString p.arity
    specTheorem := toString p.spec.specThm.name
    notes := p.spec.notes
    tags := tags
    cab_version := summary.cab_version
    foundationCommitment := summary.foundationCommitment
    rulesRoot := summary.rulesRoot
    manifestCommit := summary.manifestCommit
    kernelCommitment := summary.kernelCommitment
    proofDigest := summary.proofDigest
    traceRoot := summary.traceRoot
    transcriptRoot := summary.transcriptRoot
  }

def manifestJson : IO Json := do
  let gitRev ← gitRev?
  let entries ← Exec.allProcs.mapM entryFor
  let manifest : ProcManifest :=
    { format := HeytingLean.Exec.Manifest.manifestFormat
      manifest_version := HeytingLean.Exec.Manifest.manifestVersion
      manifest_path := HeytingLean.Exec.Manifest.manifestPath
      lean_version := Lean.versionString
      git_rev := gitRev
      processes := entries }
  pure <| toJson manifest

def outputPath : System.FilePath :=
  System.FilePath.mk ".." / HeytingLean.Exec.Manifest.manifestPath

def main (_args : List String) : IO UInt32 := do
  let j ← manifestJson
  let some dir := outputPath.parent
    | throw <| IO.userError s!"could not compute parent directory for {outputPath}"
  IO.FS.createDirAll dir
  IO.FS.writeFile outputPath j.pretty
  IO.println s!"wrote {outputPath}"
  pure 0

end ProcMetadata
end CLI
end HeytingLean

/-- Expose entry point for the Lake executable target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ProcMetadata.main args
