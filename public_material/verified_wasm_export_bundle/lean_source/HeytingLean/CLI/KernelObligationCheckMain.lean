import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.KernelAssurance.ObligationManifest
import HeytingLean.LoF.LeanKernel.VerifierObligationJson

namespace HeytingLean
namespace CLI
namespace KernelObligationCheckMain

open Lean
open HeytingLean.KernelAssurance
open HeytingLean.LoF.LeanKernel

structure CliArgs where
  artifactPath : System.FilePath := "kernel_obligations.json"
  payloadPath : Option System.FilePath := none
  jsonOutput : Bool := false
  outPath : Option System.FilePath := none
  deriving Inhabited

structure CheckReport where
  coverage : ObligationCoverageReport
  replay : ObligationReplayReport
  checker : ObligationCheckerReport
  tierDecision : TierDecision
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def usage : String :=
  String.intercalate "\n"
    [ "kernel_obligation_check - run replay and checker over a verified_check SKY obligation artifact"
    , ""
    , "Usage:"
    , "  lake exe kernel_obligation_check -- --artifact kernel_obligations.json --json"
    , ""
    , "Options:"
    , "  --artifact <path>"
    , "  --payload <path>"
    , "  --out <path>"
    , "  --json"
    ]

private partial def parseArgs (args : List String) (cfg : CliArgs := default) : Except String CliArgs := do
  match args with
  | [] => pure cfg
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => throw "help"
  | "--artifact" :: path :: rest => parseArgs rest { cfg with artifactPath := path }
  | "--payload" :: path :: rest => parseArgs rest { cfg with payloadPath := some path }
  | "--out" :: path :: rest => parseArgs rest { cfg with outPath := some path }
  | "--json" :: rest => parseArgs rest { cfg with jsonOutput := true }
  | bad :: _ => throw s!"unknown arg: {bad}"

private def readArtifact (path : System.FilePath) : IO VerifierArtifact := do
  let contents ← IO.FS.readFile path
  let json ←
    match Json.parse contents with
    | .ok json => pure json
    | .error err => throw <| IO.userError s!"failed to parse JSON artifact: {err}"
  match parseVerifierArtifact json with
  | .ok artifact => pure artifact
  | .error err => throw <| IO.userError s!"failed to decode verifier artifact: {err}"

private def readJsonFile (path : System.FilePath) : IO Json := do
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | .ok json => pure json
  | .error err => throw <| IO.userError s!"failed to parse JSON file: {err}"

private def mkReport (artifact : VerifierArtifact) (sourcePayload? : Option Json := none) : CheckReport :=
  let bundle := ObligationSliceBundle.ofArtifact artifact
  let coverage := ObligationCoverageReport.ofBundleWithSourcePayload bundle sourcePayload?
  let replay := ObligationReplayReport.ofBundle bundle
  let checker := ObligationCheckerReport.ofBundle bundle
  let tierDecision := decideObligationTier .slice_checker_certified coverage replay checker
  { coverage := coverage, replay := replay, checker := checker, tierDecision := tierDecision }

private def renderText (report : CheckReport) : String :=
  String.intercalate "\n"
    [ s!"bundleDigest: {report.coverage.bundleDigest}"
    , s!"coverage: discovered={report.coverage.discoveredObligations} exported={report.coverage.exportedObligations} supported={report.coverage.supportedObligations} blocked={report.coverage.blockedObligations} unclassified={report.coverage.unclassifiedObligations}"
    , s!"replay: checked={report.replay.checked} passed={report.replay.passed} failed={report.replay.failed}"
    , s!"checker: checked={report.checker.checked} passed={report.checker.passed} failed={report.checker.failed}"
    , s!"tier: {report.tierDecision.granted}"
    , s!"reason: {report.tierDecision.reason}"
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
  let artifact ← readArtifact args.artifactPath
  let sourcePayload? ← args.payloadPath.mapM readJsonFile
  let report := mkReport artifact sourcePayload?
  let rendered := if args.jsonOutput then (Lean.toJson report).pretty else renderText report
  match args.outPath with
  | some outPath => IO.FS.writeFile outPath rendered
  | none => pure ()
  IO.println rendered
  return 0

end KernelObligationCheckMain
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.KernelObligationCheckMain.mainImpl argv
