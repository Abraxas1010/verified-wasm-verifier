import Lean
import HeytingLean.EndToEnd.Manifest
import HeytingLean.EndToEnd.ManifestData
import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Theorems.Core
import HeytingLean.Theorems.Core
import HeytingLean.Exec.Manifest

namespace HeytingLean
namespace TCB

open Lean
open HeytingLean.EndToEnd
open HeytingLean.EndToEnd.Manifest
open HeytingLean.Meta.LeanTT0

/-- Hex-encode a byte array with a 0x prefix. -/
private def hexOfBA (ba : ByteArray) : String :=
  let parts := ba.toList.map (fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s)
  "0x" ++ String.intercalate "" parts

/-- On-disk path (from the repository root) for the CAB JSON. -/
def cabRelPath : String := "artifacts/cab.json"

/-- Filesystem path to the CAB JSON when running from `lean/`. -/
def cabFsPath : System.FilePath := System.FilePath.mk ".." / cabRelPath

/-- Optional kernel commit file path (if emitted separately). -/
def kernelRelPath : String := "artifacts/kernel.json"

/-- Filesystem path to the kernel JSON when running from `lean/`. -/
def kernelFsPath : System.FilePath := System.FilePath.mk ".." / kernelRelPath

/-- Relative path to theorems manifest (from repo root). -/
def theoremsManifestRelPath : String := HeytingLean.Theorems.manifestPath

/-- Filesystem path to the theorems manifest when running from `lean/`. -/
def theoremsManifestFsPath : System.FilePath :=
  System.FilePath.mk ".." / theoremsManifestRelPath

/-- Relative path to processes manifest (from repo root). -/
def processesManifestRelPath : String := HeytingLean.Exec.Manifest.manifestPath

/-- Filesystem path to the processes manifest when running from `lean/`. -/
def processesManifestFsPath : System.FilePath :=
  System.FilePath.mk ".." / processesManifestRelPath
/-- Basic compiler metadata captured for provenance. -/
structure CompilerInfo where
  name : String
  version : String
  flags : String
  deriving Repr, Inhabited

/-- Describes which backend the build is targeting (Lean C, LambdaIR, CompCert, etc.). -/
structure BackendInfo where
  type : String
  details : String
  deriving Repr, Inhabited

/-- Human-readable summary of a proven property from the manifest. -/
structure ExampleProp where
  theoremName : String
  description : String
  deriving Repr, Inhabited

/-- Minimal example entry captured inside the TCB metadata. -/
structure ExampleEntry where
  category : String
  name : String
  arity : Nat
  paramNames : List String
  leanSymbol : String
  irSymbol : String
  cFunction : String
  endToEndTheorem : String
  properties : List ExampleProp
  deriving Repr, Inhabited

/-- Examples block that mirrors the standalone examples manifest. -/
structure ExamplesMetadata where
  manifestVersion : String
  manifestFormat : String
  manifestPath : String
  entries : List ExampleEntry
  deriving Repr, Inhabited

/-- Reference to the on-disk examples manifest. -/
structure ExamplesManifestRef where
  format : String
  path : String
  sha256 : String
  deriving Repr, Inhabited

/-- Summary of theorems manifest (format + counts). -/
structure TheoremsMetadata where
  format : String
  manifestVersion : String
  manifestPath : String
  theoremCount : Nat
  deriving Repr, Inhabited

/-- Pointer + hash for the theorems manifest artifact. -/
structure TheoremsManifestRef where
  path : String
  sha256 : String
  deriving Repr, Inhabited

/-- Summary of processes manifest (format + counts). -/
structure ProcessesMetadata where
  format : String
  manifestVersion : String
  manifestPath : String
  processCount : Nat
  deriving Repr, Inhabited

/-- Pointer + hash for the processes manifest artifact. -/
structure ProcessesManifestRef where
  path : String
  sha256 : String
  deriving Repr, Inhabited

/-- Parsed view of `cab.json`. -/
structure CabFile where
  version : String
  foundationCommitment : String
  rulesRoot : String
  rulesRootPoseidon : String
  manifestCommit : String
  deriving Repr, Inhabited

/-- CAB metadata included in `tcb_metadata.json`. -/
structure CabMeta where
  version : String
  foundationCommitment : String
  rulesRoot : String
  manifestCommit : String
  kernelCommitment : String
  deriving Repr, Inhabited

/-- Pointer + hash for the CAB artifact. -/
structure CabPointer where
  path : String
  sha256 : String
  deriving Repr, Inhabited

/-- Canonical trusted-computing-base metadata emitted after every strict build. -/
structure Metadata where
  leanVersion : String
  mathlibCommit : String
  projectCommit : String
  compiler : CompilerInfo
  backend : BackendInfo
  os : String
  arch : String
  timestamp : String
  examples : ExamplesMetadata
  examplesManifest : ExamplesManifestRef
  theorems : TheoremsMetadata
  theoremsManifest : TheoremsManifestRef
  processes : ProcessesMetadata
  processesManifest : ProcessesManifestRef
  cab : CabMeta
  cabPointer : CabPointer
  deriving Repr, Inhabited

private def envOrDefault (key default : String) : IO String := do
  match (← IO.getEnv key) with
  | some val => pure val
  | none => pure default

private def firstEnv? (keys : List String) : IO (Option String) := do
  for key in keys do
    if let some val ← IO.getEnv key then
      if !val.trim.isEmpty then
        return some val
  return none

private def runCmd? (cmd : String) (args : List String) : IO (Option String) := do
  try
    let output ← IO.Process.output { cmd := cmd, args := args.toArray }
    if output.exitCode == 0 then
      let trimmed := output.stdout.trim
      return if trimmed.isEmpty then none else some trimmed
    else
      return none
  catch _ =>
    return none

private def detectProjectCommit : IO String := do
  match ← runCmd? "git" ["rev-parse", "HEAD"] with
  | some hash => pure hash
  | none => pure "unknown"

private def detectMathlibCommit : IO String := do
  match ← firstEnv? ["MATHLIB_COMMIT", "HEYTING_MATHLIB"] with
  | some val => pure val
  | none => pure "unknown"

private def detectCompilerInfo : IO CompilerInfo := do
  let name ← envOrDefault "HEYTING_C_COMPILER" (← envOrDefault "CC" "clang")
  let rawVersion ← runCmd? name ["--version"]
  let version :=
    match rawVersion with
    | some txt =>
      match txt.splitOn "\n" with
      | head :: _ => head
      | [] => txt
    | none => "unknown"
  let flags ← envOrDefault "HEYTING_C_FLAGS" (← envOrDefault "CFLAGS" "")
  pure { name, version, flags }

private def detectBackendInfo : IO BackendInfo := do
  let bType ← envOrDefault "HEYTING_BACKEND" "lean-c"
  let details ← envOrDefault "HEYTING_BACKEND_DETAILS" "initial pipeline"
  pure { type := bType, details }

private def detectOS : IO String := do
  match ← firstEnv? ["HEYTING_OS", "OSTYPE", "OS"] with
  | some val => pure val
  | none =>
    match ← runCmd? "uname" ["-s"] with
    | some v => pure v
    | none => pure "unknown"

private def detectArch : IO String := do
  match ← firstEnv? ["HEYTING_ARCH", "ARCH", "PROCESSOR", "HOSTTYPE"] with
  | some val => pure val
  | none =>
    match ← runCmd? "uname" ["-m"] with
    | some v => pure v
    | none => pure "unknown"

private def detectTimestamp : IO String := do
  match ← runCmd? "date" ["-u", "+%Y-%m-%dT%H:%M:%SZ"] with
  | some stamp => pure stamp
  | none => pure (toString (← IO.monoNanosNow))

private def sha256File (path : System.FilePath) : IO String := do
  try
    let output ← IO.Process.output
      { cmd := "sha256sum", args := #[path.toString] }
    if output.exitCode = 0 then
      match output.stdout.splitOn " " with
      | h :: _ => pure h
      | _ => pure "unknown"
    else
      pure "unknown"
  catch _ =>
    pure "unknown"

private def parseCabJson (j : Json) : IO CabFile := do
  let getStr (k : String) : IO String := do
    match j.getObjVal? k with
    | .ok (.str s) => pure s
    | _ => throw <| IO.userError s!"cab.json: missing or invalid field '{k}'"
  let version ← getStr "version"
  let foundationCommitment ← getStr "foundationCommitment"
  let rulesRoot ← getStr "rulesRoot"
  let manifestCommit ← getStr "manifestCommit"
  let rulesRootPoseidon ←
    match j.getObjVal? "rulesRoot_poseidon" with
    | .ok (.str s) => pure s
    | _ => pure ""
  pure {
    version, foundationCommitment, rulesRoot, manifestCommit, rulesRootPoseidon
  }

private def readCabFile : IO CabFile := do
  if !(← System.FilePath.pathExists cabFsPath) then
    throw <| IO.userError s!"cab.json not found at {cabFsPath}; run `lake exe cab_mint -- --out ../artifacts` first"
  let contents ← IO.FS.readFile cabFsPath
  let j ←
    match Json.parse contents with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"Failed to parse cab.json: {e}"
  parseCabJson j

private def readKernelCommitment? : IO (Option String) := do
  if !(← System.FilePath.pathExists kernelFsPath) then
    return none
  let contents ← IO.FS.readFile kernelFsPath
  let j ← match Json.parse contents with
    | .ok j => pure j
    | .error _ => return none
  pure <|
    match j.getObjVal? "kernelCommitment" with
    | .ok (.str s) => some s
    | _ => none

-- Canonical descriptor kept in sync with KernelCommitMain.
private def kernelDescriptor : String :=
  "Kernel:TT0.kernel:v1;rules=[BetaLamApp,DeltaPrimNatAdd];semantics=det"

private def kernelCommitmentHex : String :=
  hexOfBA (sha256 kernelDescriptor.toUTF8)

private def detectCabMeta : IO CabMeta := do
  let cab ← readCabFile
  let kernel ←
    match ← readKernelCommitment? with
    | some k => pure k
    | none => pure kernelCommitmentHex
  pure {
    version := cab.version
    foundationCommitment := cab.foundationCommitment
    rulesRoot := cab.rulesRoot
    manifestCommit := cab.manifestCommit
    kernelCommitment := kernel
  }

private def detectCabPointer : IO CabPointer := do
  let sha ← sha256File cabFsPath
  pure { path := cabRelPath, sha256 := sha }

private def propFromManifest (p : HeytingLean.EndToEnd.ProvenProp) :
    ExampleProp :=
  { theoremName := p.theoremName
    description := p.description }

private def exampleFromSummary (ex : HeytingLean.EndToEnd.ExampleSummary) :
    ExampleEntry :=
  { category := ex.category
    name := ex.name
    arity := ex.arity
    paramNames := ex.paramNames
    leanSymbol := ex.leanName
    irSymbol := ex.irName
    cFunction := ex.cFunName
    endToEndTheorem := ex.endToEndName
    properties := ex.provenProps.map propFromManifest }

private def detectExamples : ExamplesMetadata :=
  { manifestVersion := manifestVersion
    manifestFormat := manifestFormat
    manifestPath := manifestPath
    entries := HeytingLean.EndToEnd.Manifest.allExamples.map exampleFromSummary }

private def detectExamplesManifestRef : IO ExamplesManifestRef := do
  let path := (System.FilePath.mk ".." / manifestPath)
  let sha ← sha256File path
  pure { format := manifestFormat, path := manifestPath, sha256 := sha }

private def detectTheorems : IO TheoremsMetadata := do
  if !(← System.FilePath.pathExists theoremsManifestFsPath) then
    throw <| IO.userError s!"theorems manifest not found at {theoremsManifestFsPath}; run `lake exe theorem_metadata` first"
  let contents ← IO.FS.readFile theoremsManifestFsPath
  let j ← match Json.parse contents with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"Failed to parse theorems manifest: {e}"
  let getStr (k : String) : IO String := do
    match j.getObjVal? k with
    | .ok (.str s) => pure s
    | _ => throw <| IO.userError s!"theorems manifest: missing or invalid '{k}'"
  let format ← getStr "format"
  let manifestVersion ← getStr "manifest_version"
  let manifestPath ← getStr "manifest_path"
  let thmsArr ←
    match j.getObjVal? "theorems" with
    | .ok (.arr a) => pure a
    | _ => throw <| IO.userError "theorems manifest: missing 'theorems' array"
  pure {
    format
    manifestVersion
    manifestPath
    theoremCount := thmsArr.size
  }

private def detectTheoremsManifestRef : IO TheoremsManifestRef := do
  if !(← System.FilePath.pathExists theoremsManifestFsPath) then
    throw <| IO.userError s!"theorems manifest not found at {theoremsManifestFsPath}; run `lake exe theorem_metadata` first"
  let sha ← sha256File theoremsManifestFsPath
  pure { path := theoremsManifestRelPath, sha256 := sha }

private def detectProcesses : IO ProcessesMetadata := do
  if !(← System.FilePath.pathExists processesManifestFsPath) then
    throw <| IO.userError s!"processes manifest not found at {processesManifestFsPath}; run `lake exe proc_metadata` first"
  let contents ← IO.FS.readFile processesManifestFsPath
  let j ← match Json.parse contents with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"Failed to parse processes manifest: {e}"
  let getStr (k : String) : IO String := do
    match j.getObjVal? k with
    | .ok (.str s) => pure s
    | _ => throw <| IO.userError s!"processes manifest: missing or invalid '{k}'"
  let format ← getStr "format"
  let manifestVersion ← getStr "manifest_version"
  let manifestPath ← getStr "manifest_path"
  let procsArr ←
    match j.getObjVal? "processes" with
    | .ok (.arr a) => pure a
    | _ => throw <| IO.userError "processes manifest: missing 'processes' array"
  pure {
    format
    manifestVersion
    manifestPath
    processCount := procsArr.size
  }

private def detectProcessesManifestRef : IO ProcessesManifestRef := do
  if !(← System.FilePath.pathExists processesManifestFsPath) then
    throw <| IO.userError s!"processes manifest not found at {processesManifestFsPath}; run `lake exe proc_metadata` first"
  let sha ← sha256File processesManifestFsPath
  pure { path := processesManifestRelPath, sha256 := sha }

/-- Collects the current metadata snapshot. -/
def current : IO Metadata := do
  let leanVersion := Lean.versionString
  let mathlibCommit ← detectMathlibCommit
  let projectCommit ← detectProjectCommit
  let compiler ← detectCompilerInfo
  let backend ← detectBackendInfo
  let os ← detectOS
  let arch ← detectArch
  let timestamp ← detectTimestamp
  let examples := detectExamples
  let examplesManifest ← detectExamplesManifestRef
  let theorems ← detectTheorems
  let theoremsManifest ← detectTheoremsManifestRef
  let processes ← detectProcesses
  let processesManifest ← detectProcessesManifestRef
  let cab ← detectCabMeta
  let cabPointer ← detectCabPointer
  pure {
    leanVersion
    mathlibCommit
    projectCommit
    compiler
    backend
    os
    arch
    timestamp
    examples
    examplesManifest
    theorems
    theoremsManifest
    processes
    processesManifest
    cab
    cabPointer
  }

namespace CompilerInfo

/-- Encode compiler info as JSON. -/
def toJson (info : CompilerInfo) : Json :=
  Json.mkObj [
    ("name", Json.str info.name),
    ("version", Json.str info.version),
    ("flags", Json.str info.flags)
  ]

end CompilerInfo

namespace BackendInfo

/-- Encode backend info as JSON. -/
def toJson (info : BackendInfo) : Json :=
  Json.mkObj [
    ("type", Json.str info.type),
    ("details", Json.str info.details)
  ]

end BackendInfo

namespace ExampleProp

/-- Encode example property as JSON. -/
def toJson (p : ExampleProp) : Json :=
  Json.mkObj [
    ("theorem_name", Json.str p.theoremName),
    ("description", Json.str p.description)
  ]

end ExampleProp

namespace ExampleEntry

/-- Encode an example entry as JSON. -/
def toJson (ex : ExampleEntry) : Json :=
  Json.mkObj [
    ("category", Json.str ex.category),
    ("name", Json.str ex.name),
    ("arity", Lean.toJson ex.arity),
    ("param_names", Json.arr (ex.paramNames.map Json.str |>.toArray)),
    ("lean_symbol", Json.str ex.leanSymbol),
    ("ir_symbol", Json.str ex.irSymbol),
    ("c_function", Json.str ex.cFunction),
    ("end_to_end_theorem", Json.str ex.endToEndTheorem),
    ("lof_props",
      Json.arr ((ex.properties.map ExampleProp.toJson).toArray))
  ]

end ExampleEntry

namespace ExamplesMetadata

/-- Encode the examples block as JSON. -/
def toJson (ex : ExamplesMetadata) : Json :=
  Json.mkObj [
    ("manifest_version", Json.str ex.manifestVersion),
    ("manifest_format", Json.str ex.manifestFormat),
    ("manifest_path", Json.str ex.manifestPath),
    ("examples", Json.arr ((ex.entries.map ExampleEntry.toJson).toArray))
  ]

end ExamplesMetadata

namespace ExamplesManifestRef

/-- Encode the manifest reference (format/path/hash) as JSON. -/
def toJson (ref : ExamplesManifestRef) : Json :=
  Json.mkObj [
    ("format", Json.str ref.format),
    ("path", Json.str ref.path),
    ("sha256", Json.str ref.sha256)
  ]

end ExamplesManifestRef

namespace TheoremsMetadata

/-- Encode theorems summary as JSON. -/
def toJson (t : TheoremsMetadata) : Json :=
  Json.mkObj [
    ("format", Json.str t.format),
    ("manifest_version", Json.str t.manifestVersion),
    ("manifest_path", Json.str t.manifestPath),
    ("theorem_count", Json.num t.theoremCount)
  ]

end TheoremsMetadata

namespace TheoremsManifestRef

/-- Encode the theorems manifest reference as JSON. -/
def toJson (ref : TheoremsManifestRef) : Json :=
  Json.mkObj [
    ("path", Json.str ref.path),
    ("sha256", Json.str ref.sha256)
  ]

end TheoremsManifestRef

namespace ProcessesMetadata

/-- Encode processes summary as JSON. -/
def toJson (p : ProcessesMetadata) : Json :=
  Json.mkObj [
    ("format", Json.str p.format),
    ("manifest_version", Json.str p.manifestVersion),
    ("manifest_path", Json.str p.manifestPath),
    ("process_count", Json.num p.processCount)
  ]

end ProcessesMetadata

namespace ProcessesManifestRef

/-- Encode the processes manifest reference as JSON. -/
def toJson (ref : ProcessesManifestRef) : Json :=
  Json.mkObj [
    ("path", Json.str ref.path),
    ("sha256", Json.str ref.sha256)
  ]

end ProcessesManifestRef

namespace CabMeta

/-- Encode CAB metadata as JSON. -/
def toJson (c : CabMeta) : Json :=
  Json.mkObj [
    ("version", Json.str c.version),
    ("foundationCommitment", Json.str c.foundationCommitment),
    ("rulesRoot", Json.str c.rulesRoot),
    ("manifestCommit", Json.str c.manifestCommit),
    ("kernelCommitment", Json.str c.kernelCommitment)
  ]

end CabMeta

namespace CabPointer

/-- Encode CAB pointer (path + hash) as JSON. -/
def toJson (p : CabPointer) : Json :=
  Json.mkObj [
    ("path", Json.str p.path),
    ("sha256", Json.str p.sha256)
  ]

end CabPointer

namespace Metadata

/-- Encode metadata as JSON matching `docs/tcb_metadata_schema.json`. -/
def toJson (m : Metadata) : Json :=
  Json.mkObj [
    ("lean_version", Json.str m.leanVersion),
    ("mathlib_commit", Json.str m.mathlibCommit),
    ("project_commit", Json.str m.projectCommit),
    ("compiler", m.compiler.toJson),
    ("backend", m.backend.toJson),
    ("os", Json.str m.os),
    ("arch", Json.str m.arch),
    ("timestamp", Json.str m.timestamp),
    ("examples", ExamplesMetadata.toJson m.examples),
    ("examples_manifest", ExamplesManifestRef.toJson m.examplesManifest),
    ("theorems", TheoremsMetadata.toJson m.theorems),
    ("theorems_manifest", TheoremsManifestRef.toJson m.theoremsManifest),
    ("processes", ProcessesMetadata.toJson m.processes),
    ("processes_manifest", ProcessesManifestRef.toJson m.processesManifest),
    ("cab", CabMeta.toJson m.cab),
    ("cab_pointer", CabPointer.toJson m.cabPointer)
  ]

/-- Convenience alias for pretty-printed JSON. -/
def toPrettyJson (m : Metadata) : String :=
  (toJson m).pretty

end Metadata

end TCB
end HeytingLean
