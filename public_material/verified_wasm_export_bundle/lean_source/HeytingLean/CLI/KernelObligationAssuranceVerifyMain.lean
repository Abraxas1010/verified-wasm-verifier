import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.KernelAssurance.ObligationAssuranceVerify

namespace HeytingLean
namespace CLI
namespace KernelObligationAssuranceVerifyMain

open Lean
open HeytingLean.KernelAssurance

structure CliArgs where
  manifestPath : Option System.FilePath := none
  cabZkPath : Option System.FilePath := none
  jsonOutput : Bool := false
  outPath : Option System.FilePath := none
  deriving Inhabited

private def usage : String :=
  String.intercalate "\n"
    [ "kernel_obligation_assurance_verify - verify base or CAB-ZK kernel obligation assurance manifests"
    , ""
    , "Usage:"
    , "  lake exe kernel_obligation_assurance_verify -- --cab-zk manifest.json --json"
    , "  lake exe kernel_obligation_assurance_verify -- --manifest base.json --cab-zk manifest.json --json"
    , ""
    , "Options:"
    , "  --manifest <path>"
    , "  --cab-zk <path>"
    , "  --out <path>"
    , "  --json"
    ]

private partial def parseArgs (args : List String) (cfg : CliArgs := default) : Except String CliArgs := do
  match args with
  | [] => pure cfg
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => throw "help"
  | "--manifest" :: path :: rest => parseArgs rest { cfg with manifestPath := some path }
  | "--cab-zk" :: path :: rest => parseArgs rest { cfg with cabZkPath := some path }
  | "--out" :: path :: rest => parseArgs rest { cfg with outPath := some path }
  | "--json" :: rest => parseArgs rest { cfg with jsonOutput := true }
  | bad :: _ => throw s!"unknown arg: {bad}"

private def readJsonAs [FromJson α] (path : System.FilePath) : IO α := do
  let contents ← IO.FS.readFile path
  let json ←
    match Json.parse contents with
    | .ok json => pure json
    | .error err => throw <| IO.userError s!"failed to parse JSON file: {err}"
  match fromJson? json with
  | .ok value => pure value
  | .error err => throw <| IO.userError s!"failed to decode JSON file: {err}"

private def renderText (report : KernelObligationAssuranceVerifyReport) : String :=
  String.intercalate "\n"
    [ s!"mode: {report.mode}"
    , s!"ok: {report.ok}"
    , s!"bundleDigest: {report.baseBundleDigest}"
    , s!"grantedTier: {report.baseGrantedTier}"
    , s!"baseTierDecisionConsistent: {report.baseTierDecisionConsistent}"
    , s!"baseClaimBoundaryConsistent: {report.baseClaimBoundaryConsistent}"
    , s!"externalBaseMatches: {report.externalBaseMatches}"
    , s!"checkerDigestMatches: {report.checkerDigestMatches}"
    , s!"grantedTierMatchesBase: {report.grantedTierMatchesBase}"
    , s!"assuranceModeConsistent: {report.assuranceModeConsistent}"
    , s!"receiptBindingsMatch: {report.receiptBindingsMatch}"
    , s!"receiptConcreteIfPresent: {report.receiptConcreteIfPresent}"
    , s!"receiptBoundaryConservative: {report.receiptBoundaryConservative}"
    , s!"failures: {String.intercalate "; " report.failures.toList}"
    ]

def mainImpl (argv : List String) : IO UInt32 := do
  let args ←
    match parseArgs (HeytingLean.CLI.stripLakeArgs argv) with
    | .ok a => pure a
    | .error "help" =>
        IO.println usage
        return 0
    | .error e =>
        throw <| IO.userError e
  let report ←
    match args.cabZkPath, args.manifestPath with
    | some cabZkPath, manifestPath? =>
        let cabZk : KernelObligationCABZKManifest ← readJsonAs cabZkPath
        let externalBase? ←
          manifestPath?.mapM fun path => do
            let manifest : KernelObligationAssuranceManifest ← readJsonAs path
            pure manifest
        pure <| KernelObligationAssuranceVerifyReport.ofCABZK cabZk externalBase?
    | none, some manifestPath =>
        let manifest : KernelObligationAssuranceManifest ← readJsonAs manifestPath
        pure <| KernelObligationAssuranceVerifyReport.ofBase manifest
    | none, none =>
        throw <| IO.userError "provide --manifest for a base manifest or --cab-zk for a CAB-ZK manifest"
  let rendered := if args.jsonOutput then (toJson report).pretty else renderText report
  match args.outPath with
  | some outPath => IO.FS.writeFile outPath rendered
  | none => pure ()
  IO.println rendered
  return if report.ok then 0 else 1

end KernelObligationAssuranceVerifyMain
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.KernelObligationAssuranceVerifyMain.mainImpl argv
