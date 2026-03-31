import Lean
import HeytingLean.Theorems.Cert

open HeytingLean.Theorems
open Lean

namespace HeytingLean
namespace CLI
namespace TheoremMetadata

def main (_args : List String) : IO UInt32 := do
  -- Prefer discovered blocks if available; fall back to seeds on error.
  let discovered ←
    try
      discoverBlocksIO
    catch _ =>
      pure #[]
  let blocks := mergeBlocks seedThmBlocks discovered
  IO.println s!"[theorem_metadata] discovered={discovered.size} merged={blocks.size}"
  let cts ← blocks.mapM (fun b => do
    let cert ← getThmCert b
    pure { block := b, cert := cert })
  let entries := cts.map toSummary
  let theoremsArr := entries.map (fun e => Lean.toJson e)
  let manifest : Json :=
    Json.mkObj [
      ("format",           Json.str manifestFormat),
      ("manifest_version", Json.str manifestVersion),
      ("manifest_path",    Json.str manifestPath),
      ("theorems",         Json.arr theoremsArr)
    ]
  let outPath := System.FilePath.mk ".." / manifestPath
  let some dir := outPath.parent
    | throw <| IO.userError s!"could not compute parent directory for {outPath}"
  IO.FS.createDirAll dir
  IO.FS.writeFile outPath manifest.pretty
  IO.println s!"wrote {outPath}"
  pure 0

end TheoremMetadata
end CLI
end HeytingLean

/-- Expose entry point for the Lake executable target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.TheoremMetadata.main args
