import Lean
import HeytingLean.Exec.Core

namespace HeytingLean.Exec
namespace Manifest

open Lean

/-- Manifest version tag for process metadata. -/
def manifestVersion : String := "1"

/-- Format tag for process manifests. -/
def manifestFormat : String := "apmt-proc-manifest-v1"

/-- Relative on-disk path (from repo root) for the processes manifest. -/
def manifestPath : String := "artifacts/processes_manifest.json"

/-- Manifest entry describing a registered executable process. -/
structure ProcManifestEntry where
  id                  : String
  arity               : String
  specTheorem         : String
  notes               : Option String
  tags                : List String
  cab_version         : String
  foundationCommitment : String
  rulesRoot           : String
  manifestCommit      : String
  kernelCommitment    : String
  proofDigest         : String
  traceRoot           : String
  transcriptRoot      : String
  deriving Repr, Lean.ToJson

/-- Top-level processes manifest. -/
structure ProcManifest where
  format           : String
  manifest_version : String
  manifest_path    : String
  lean_version     : String
  git_rev          : String
  processes        : Array ProcManifestEntry
  deriving Repr, Lean.ToJson

end Manifest
end HeytingLean.Exec
