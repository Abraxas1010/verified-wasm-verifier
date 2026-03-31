import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.KernelAssurance.Manifest

namespace HeytingLean
namespace CLI
namespace KernelSliceCheckMain

open Lean
open HeytingLean.KernelAssurance

structure CliArgs where
  bundlePath : System.FilePath := "kernel_slice_bundle.json"
  jsonOutput : Bool := false
  outPath : Option System.FilePath := none
  deriving Inhabited

structure CheckReport where
  coverage : CoverageReport
  replay : ReplayReport
  checker : CheckerReport
  tierDecision : TierDecision
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def usage : String :=
  String.intercalate "\n"
    [ "kernel_slice_check - run replay and checker over a kernel slice bundle"
    , ""
    , "Usage:"
    , "  lake exe kernel_slice_check -- --bundle kernel_slice_bundle.json --json"
    , ""
    , "Options:"
    , "  --bundle <path>"
    , "  --out <path>"
    , "  --json"
    ]

private partial def parseArgs (args : List String) (cfg : CliArgs := default) : Except String CliArgs := do
  match args with
  | [] => pure cfg
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => throw "help"
  | "--bundle" :: path :: rest => parseArgs rest { cfg with bundlePath := path }
  | "--out" :: path :: rest => parseArgs rest { cfg with outPath := some path }
  | "--json" :: rest => parseArgs rest { cfg with jsonOutput := true }
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

private def mkReport (bundle : SliceBundle) : CheckReport :=
  let coverage := CoverageReport.ofBundle bundle
  let replay := ReplayReport.ofBundle bundle
  let checker := CheckerReport.ofBundle bundle
  let tierDecision := decideTier .slice_checker_certified coverage replay checker
  { coverage := coverage, replay := replay, checker := checker, tierDecision := tierDecision }

private def renderText (report : CheckReport) : String :=
  String.intercalate "\n"
    [ s!"bundleDigest: {report.coverage.bundleDigest}"
    , s!"coverage: supported={report.coverage.supportedDecls} blocked={report.coverage.blockedDecls} unclassified={report.coverage.unclassifiedDecls}"
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
  let bundle ← readBundle args.bundlePath
  let report := mkReport bundle
  let rendered := if args.jsonOutput then (Lean.toJson report).pretty else renderText report
  match args.outPath with
  | some outPath => IO.FS.writeFile outPath rendered
  | none => pure ()
  IO.println rendered
  return 0

end KernelSliceCheckMain
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.KernelSliceCheckMain.mainImpl argv
