import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.KernelAssurance.Coverage

namespace HeytingLean
namespace CLI
namespace KernelCoverageMain

open Lean
open HeytingLean.KernelAssurance

structure CliArgs where
  bundlePath : System.FilePath := "kernel_slice_bundle.json"
  jsonOutput : Bool := false
  outPath : Option System.FilePath := none
  deriving Inhabited

private def usage : String :=
  String.intercalate "\n"
    [ "kernel_coverage - emit the coverage ledger for a kernel slice bundle"
    , ""
    , "Usage:"
    , "  lake exe kernel_coverage -- --bundle kernel_slice_bundle.json --json"
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

private def renderText (report : CoverageReport) : String :=
  String.intercalate "\n"
    [ s!"bundleDigest: {report.bundleDigest}"
    , s!"families: discovered={report.discoveredFamilyCount} blocked={report.blockedFamilyCount} unclassified={report.unclassifiedFamilyCount}"
    , s!"decls: total={report.declsTotal} supported={report.supportedDecls} blocked={report.blockedDecls} unclassified={report.unclassifiedDecls}"
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
  let report := CoverageReport.ofBundle bundle
  let rendered := if args.jsonOutput then (Lean.toJson report).pretty else renderText report
  match args.outPath with
  | some outPath => IO.FS.writeFile outPath rendered
  | none => pure ()
  IO.println rendered
  return 0

end KernelCoverageMain
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.KernelCoverageMain.mainImpl argv
