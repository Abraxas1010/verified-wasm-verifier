import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.KernelAssurance.Manifest

namespace HeytingLean
namespace CLI
namespace KernelAssuranceMintMain

open Lean
open HeytingLean.KernelAssurance

structure CliArgs where
  bundlePath : System.FilePath := "kernel_slice_bundle.json"
  outPath : System.FilePath := "kernel_assurance_manifest.json"
  requested : AssuranceTier := .slice_replayed
  foundationCommitment : Option String := none
  rulesRoot : Option String := none
  kernelCommitment : Option String := none
  deriving Inhabited

private def usage : String :=
  String.intercalate "\n"
    [ "kernel_assurance_mint - mint a CAB-aligned kernel assurance manifest"
    , ""
    , "Usage:"
    , "  lake exe kernel_assurance_mint -- --bundle kernel_slice_bundle.json --claim slice_replayed"
    , ""
    , "Options:"
    , "  --bundle <path>"
    , "  --out <path>"
    , "  --claim <none|slice_replayed|slice_checker_certified>"
    , "  --foundation <hex>"
    , "  --rules-root <hex>"
    , "  --kernel <hex>"
    ]

private partial def parseArgs (args : List String) (cfg : CliArgs := default) : Except String CliArgs := do
  match args with
  | [] => pure cfg
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => throw "help"
  | "--bundle" :: path :: rest => parseArgs rest { cfg with bundlePath := path }
  | "--out" :: path :: rest => parseArgs rest { cfg with outPath := path }
  | "--claim" :: claim :: rest =>
      match AssuranceTier.ofString? claim with
      | some requested => parseArgs rest { cfg with requested := requested }
      | none => throw s!"unknown claim tier: {claim}"
  | "--foundation" :: value :: rest => parseArgs rest { cfg with foundationCommitment := some value }
  | "--rules-root" :: value :: rest => parseArgs rest { cfg with rulesRoot := some value }
  | "--kernel" :: value :: rest => parseArgs rest { cfg with kernelCommitment := some value }
  | bad :: _ => throw s!"unknown arg: {bad}"

private def readBundle (path : System.FilePath) : IO SliceBundle := do
  let contents ← IO.FS.readFile path
  let json ←
    match Json.parse contents with
    | .ok json => pure json
    | .error err => throw <| IO.userError s!"failed to parse JSON bundle: {err}"
  match Lean.fromJson? json with
  | .ok bundle => pure bundle
  | .error err => throw <| IO.userError s!"failed to decode slice bundle: {err}"

private def readObjField? (path : System.FilePath) (field : String) : IO (Option String) := do
  if !(← path.pathExists) then
    return none
  let contents ← IO.FS.readFile path
  let json ←
    match Json.parse contents with
    | .ok json => pure json
    | .error _ => return none
  match json.getObjVal? field with
  | .ok (.str value) => pure (some value)
  | _ => pure none

private def readCommitments (args : CliArgs) : IO (String × String × String) := do
  let foundation ←
    match args.foundationCommitment with
    | some value => pure value
    | none => pure ((← readObjField? (System.FilePath.mk "../artifacts/cab.json") "foundationCommitment").getD "0x")
  let rulesRoot ←
    match args.rulesRoot with
    | some value => pure value
    | none => pure ((← readObjField? (System.FilePath.mk "../artifacts/cab.json") "rulesRoot").getD "0x")
  let kernelCommitment ←
    match args.kernelCommitment with
    | some value => pure value
    | none => pure ((← readObjField? (System.FilePath.mk "../artifacts/kernel.json") "kernelCommitment").getD "0x")
  pure (foundation, rulesRoot, kernelCommitment)

def mainImpl (argv : List String) : IO UInt32 := do
  let args ←
    match parseArgs (HeytingLean.CLI.stripLakeArgs argv) with
    | .ok a => pure a
    | .error "help" =>
        IO.println usage
        return 0
    | .error e =>
        throw <| IO.userError e
  let bundle ← readBundle args.bundlePath
  let (foundationCommitment, rulesRoot, kernelCommitment) ← readCommitments args
  let manifest :=
    KernelAssuranceManifest.ofBundle bundle foundationCommitment rulesRoot kernelCommitment args.requested
  IO.FS.writeFile args.outPath (Lean.toJson manifest).pretty
  IO.println s!"Wrote kernel assurance manifest to {args.outPath}"
  IO.println s!"Granted tier: {manifest.tierDecision.granted}"
  return 0

end KernelAssuranceMintMain
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.KernelAssuranceMintMain.mainImpl argv
