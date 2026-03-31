import HeytingLean.CLI.Args
import HeytingLean.Genesis.EigenformSoup.NoncomputableBridge

/-!
# EigenformSoup noncomputable bridge card exporter

Emits a compact bridge artifact that ties executable LES lanes to theorem-level
noncomputable obligations.
-/

namespace HeytingLean.CLI.EigenformSoupBridgeCardMain

open System
open HeytingLean.Genesis.EigenformSoup

private def usage : String :=
  String.intercalate "\n"
    [ "eigenform_soup_bridge_card"
    , "  Export noncomputable/theorem bridge card for LES protocol manifests."
    , ""
    , "Options:"
    , "  --out-dir <path> | --out-dir=<path>    output directory (default: dist/eigenform_soup_bridge_card)"
    , "  --help                                 show this message"
    ]

private def hasFlag (argv : List String) (flag : String) : Bool :=
  argv.any (· = flag)

private def findOptValue (argv : List String) (key : String) : Option String :=
  let keyEq := key ++ "="
  let rec go : List String → Option String
    | [] => none
    | x :: xs =>
        if x.startsWith keyEq then
          some (x.drop keyEq.length)
        else if x = key then
          match xs with
          | y :: _ => some y
          | [] => none
        else
          go xs
  go argv

private def parseOutDir (argv : List String) : FilePath :=
  let raw := (findOptValue argv "--out-dir").getD "dist/eigenform_soup_bridge_card"
  FilePath.mk raw

private def writeBridgeCard (outDir : FilePath) : IO Unit := do
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "bridge_card.json") bridgeCardJson
  IO.FS.writeFile (outDir / "bridge_card.sha256") s!"{bridgeCardSha256}\n"

def main (argv0 : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs argv0
  if hasFlag argv "--help" then
    IO.println usage
    return 0
  let outDir := parseOutDir argv
  try
    writeBridgeCard outDir
    IO.println s!"eigenform_soup_bridge_card: wrote bridge card"
    IO.println s!"out_dir={outDir}"
    IO.println s!"bridge_card={outDir / "bridge_card.json"}"
    IO.println s!"bridge_sha256={bridgeCardSha256}"
    return 0
  catch e =>
    IO.eprintln s!"eigenform_soup_bridge_card: failed: {e}"
    return 1

end HeytingLean.CLI.EigenformSoupBridgeCardMain

open HeytingLean.CLI.EigenformSoupBridgeCardMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.EigenformSoupBridgeCardMain.main args
