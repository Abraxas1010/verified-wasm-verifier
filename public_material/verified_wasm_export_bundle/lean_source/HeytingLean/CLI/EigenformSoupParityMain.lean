import HeytingLean.CLI.Args
import HeytingLean.Genesis.EigenformSoup.Extraction

/-!
# EigenformSoup runtime parity bundle generator

Emits a tiny C bundle for runtime parity smoke checks:
- `kernel.c`   : generated via `renderC count`
- `driver.c`   : calls `eigenform_soup_stabilized_count()`
- `expected.txt` : expected decimal output

This executable is intentionally lightweight and executable, while the full LES
runner remains proof-oriented (`runSoup`/`compileSoupCAB` are noncomputable).
-/

namespace HeytingLean.CLI.EigenformSoupParityMain

open System
open HeytingLean.Genesis.EigenformSoup

private def usage : String :=
  String.intercalate "\n"
    [ "eigenform_soup_parity"
    , "  Generates a runtime parity C bundle for EigenformSoup count payloads."
    , ""
    , "Options:"
    , "  --count <nat> | --count=<nat>      stabilized count payload (default: 0)"
    , "  --out-dir <path> | --out-dir=<path> output directory (default: dist/eigenform_soup_parity)"
    , "  --help                              show this message"
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

private def parseCount (argv : List String) : Except String Nat := do
  match findOptValue argv "--count" with
  | none => pure 0
  | some raw =>
      match raw.toNat? with
      | some n => pure n
      | none => throw s!"invalid --count value: {raw}"

private def parseOutDir (argv : List String) : FilePath :=
  let raw := (findOptValue argv "--out-dir").getD "dist/eigenform_soup_parity"
  FilePath.mk raw

private def driverSource : String :=
  String.intercalate "\n"
    [ "#include <stdio.h>"
    , "int eigenform_soup_stabilized_count(void);"
    , "int main(void) {"
    , "  printf(\"%d\", eigenform_soup_stabilized_count());"
    , "  return 0;"
    , "}"
    , ""
    ]

private def writeBundle (outDir : FilePath) (count : Nat) : IO Unit := do
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "kernel.c") (renderC count)
  IO.FS.writeFile (outDir / "driver.c") driverSource
  IO.FS.writeFile (outDir / "expected.txt") s!"{count}\n"

def main (argv0 : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs argv0
  if hasFlag argv "--help" then
    IO.println usage
    return 0
  match parseCount argv with
  | .error err =>
      IO.eprintln s!"eigenform_soup_parity: {err}"
      IO.eprintln "use --help for usage"
      return 2
  | .ok count =>
      let outDir := parseOutDir argv
      try
        writeBundle outDir count
        IO.println s!"eigenform_soup_parity: wrote bundle"
        IO.println s!"out_dir={outDir}"
        IO.println s!"count={count}"
        return 0
      catch e =>
        IO.eprintln s!"eigenform_soup_parity: failed: {e}"
        return 1

end HeytingLean.CLI.EigenformSoupParityMain

open HeytingLean.CLI.EigenformSoupParityMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.EigenformSoupParityMain.main args
