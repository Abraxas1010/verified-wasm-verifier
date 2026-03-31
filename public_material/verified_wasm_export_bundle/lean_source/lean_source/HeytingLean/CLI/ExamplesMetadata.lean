import Lean
import HeytingLean.EndToEnd.Manifest
import HeytingLean.EndToEnd.ManifestData

open Lean
open System
open HeytingLean.EndToEnd
open HeytingLean.EndToEnd.Manifest

namespace HeytingLean
namespace CLI
namespace ExamplesMetadata

def propToJson (p : ProvenProp) : Json :=
  Json.mkObj
    [ ("theorem_name", Json.str p.theoremName)
    , ("description", Json.str p.description) ]

def exampleToJson (ex : ExampleSummary) : Json :=
  Json.mkObj
    [ ("category", Json.str ex.category)
    , ("name", Json.str ex.name)
    , ("arity", toJson ex.arity)
    , ("param_names", Json.arr (ex.paramNames.map Json.str |>.toArray))
    , ("lean_symbol", Json.str ex.leanName)
    , ("ir_symbol", Json.str ex.irName)
    , ("c_function", Json.str ex.cFunName)
    , ("end_to_end_theorem", Json.str ex.endToEndName)
    , ("lof_props",
        Json.arr ((ex.provenProps.map propToJson).toArray))
    ]

def gitRev? : IO String := do
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

def metadataJson : IO Json := do
  let gitRev ← gitRev?
  let leanVersion := Lean.versionString
  pure <|
    Json.mkObj
      [ ("format", Json.str manifestFormat)
      , ("manifest_version", Json.str manifestVersion)
      , ("manifest_path", Json.str manifestPath)
      , ("lean_version", Json.str leanVersion)
      , ("git_rev", Json.str gitRev)
      , ("examples",
          Json.arr ((Manifest.allExamples.map exampleToJson).toArray)) ]

def outputPath : System.FilePath :=
  (System.FilePath.mk ".." / "artifacts" / "examples_manifest.json")

def main (_args : List String) : IO UInt32 := do
  let manifest ← metadataJson
  let some dir := outputPath.parent
    | throw <|
        IO.userError s!"could not compute parent directory for {outputPath}"
  IO.FS.createDirAll dir
  IO.FS.writeFile outputPath manifest.pretty
  IO.println s!"wrote {outputPath}"
  pure 0

end ExamplesMetadata
end CLI
end HeytingLean

/-- Expose entry point for the Lake executable target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ExamplesMetadata.main args
