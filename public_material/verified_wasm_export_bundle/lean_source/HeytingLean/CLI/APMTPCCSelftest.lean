import Lean
import HeytingLean.PCC.API

open Lean
open System
open HeytingLean
open HeytingLean.PCC

namespace HeytingLean.CLI
namespace APMTPCCSelftest

structure CliOpts where
  input : Option FilePath := none
  stdin : Bool := false
deriving Inhabited

private def usage : String :=
  "apmt_pcc_selftest [--input <path> | --stdin]\n" ++
  "  default: built-in selftest request"

def parseArgs : List String → Except String CliOpts
  | [] => return {}
  | "--input" :: path :: rest =>
      return { (← parseArgs rest) with input := some ⟨path⟩ }
  | "--stdin" :: rest =>
      return { (← parseArgs rest) with stdin := true }
  | flag :: _ => throw s!"unknown option: {flag}"

private def readRequest (opts : CliOpts) : IO String := do
  if opts.stdin then
    (← IO.getStdin).readToEnd
  else if let some fp := opts.input then
    IO.FS.readFile fp
  else
    pure sampleRequest.compress

private def evaluate (raw : String) : IO String := do
  let bytes := raw.toUTF8
  match String.fromUTF8? (← apmtPccEvalJson bytes) with
  | some s => pure s
  | none   => throw <| IO.userError "gateway returned invalid UTF-8"

def runWithArgs (args : List String) : IO UInt32 := do
  if args.any (· = "--help") || args.any (· = "-h") then
    IO.println usage
    return 0
  match parseArgs args with
  | Except.ok opts =>
      let req ← readRequest opts
      let out ← evaluate req
      IO.println out
      return 0
  | Except.error msg =>
      IO.eprintln s!"argument error: {msg}"
      IO.eprintln usage
      return 2

end APMTPCCSelftest
end HeytingLean.CLI

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.APMTPCCSelftest.runWithArgs args
