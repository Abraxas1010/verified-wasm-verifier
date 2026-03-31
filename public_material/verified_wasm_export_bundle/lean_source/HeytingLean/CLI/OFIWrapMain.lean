import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args

namespace HeytingLean.CLI.OFIWrapMain

open Lean

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest => if x = flag then some y else parseArg (y :: rest) flag
  | _ => none

private def splitPlus (s : String) : List String :=
  s.splitOn "+" |>.map (·.trim) |>.filter (· ≠ "")

private def splitComma (s : String) : List String :=
  s.splitOn "," |>.map (·.trim) |>.filter (· ≠ "")

private def quickOFI (tokens : List String) : Nat :=
  if tokens.isEmpty then 0 else tokens.length - 1

private def setOFI (tokens : List String) (uAtoms : List String) : Nat :=
  if uAtoms = [] then 0
  else if uAtoms.all (fun a => tokens.contains a) then 0 else 1

private def usage : String :=
  String.intercalate "\n"
    [ "ofi_wrap"
    , ""
    , "A lightweight OFI wrapper over tokenized targets."
    , ""
    , "Usage:"
    , "  ofi_wrap --target alpha+beta --U alpha,beta"
    ]

def run (argv : List String) : IO Unit := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  if argv.contains "--help" || argv.contains "-h" then
    IO.println usage
    return
  let tgt := (parseArg argv "--target").getD "alpha+beta"
  let uStr := (parseArg argv "--U").getD "alpha"
  let toks := splitPlus tgt
  let uAtoms := splitComma uStr
  let j := Json.mkObj
    [ ("mode", Json.str "ofi_wrap")
    , ("target", Json.arr (toks.toArray.map Json.str))
    , ("U", Json.arr (uAtoms.toArray.map Json.str))
    , ("ofiIndexQuick", Json.num (quickOFI toks))
    , ("ofiIndexSet", Json.num (setOFI toks uAtoms))
    , ("stable", Json.bool true)
    ]
  IO.println j.pretty

end HeytingLean.CLI.OFIWrapMain

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.OFIWrapMain.run argv
