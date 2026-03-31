import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.EvmTrace.Json
import HeytingLean.BountyHunter.EvmTrace.CEI

open IO
open Lean
open HeytingLean.BountyHunter.EvmTrace

private def usage : String :=
  String.intercalate "\n"
    [ "usage:"
    , "  evm_trace_order_check --trace <trace.json>"
    , ""
    , "outputs:"
    , "- canonical JSON containing {ok, firstWrite, firstBoundary}"
    ]

private def getArgValue? (flag : String) (args : List String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | a :: b :: rest => if a = flag then some b else go (b :: rest)
    | [_] => none
  go args

private def hasFlag (flag : String) (args : List String) : Bool :=
  args.any (fun a => a = flag)

private def readFileE (path : System.FilePath) : IO (Except String String) := do
  try
    let s ← IO.FS.readFile path
    pure (.ok s)
  catch e =>
    pure (.error s!"read error at {path}: {e}")

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  if args.isEmpty || hasFlag "--help" args || hasFlag "-h" args then
    IO.println usage
    return 0
  match getArgValue? "--trace" args with
  | none =>
      IO.eprintln usage
      return 1
  | some p =>
      match (← readFileE (System.FilePath.mk p)) with
      | .error e =>
          IO.eprintln e
          return 1
      | .ok txt =>
          match Json.parse txt with
          | .error e =>
              IO.eprintln s!"json parse error: {e}"
              return 1
          | .ok j =>
              match traceOfJsonE j with
              | .error e =>
                  IO.eprintln e
                  return 1
              | .ok t =>
                  let s := ceiOrderSummary t
                  let out :=
                    Json.mkObj
                      [ ("version", Json.str "evm_trace_order_check.v0")
                      , ("ok", Json.bool s.ok)
                      , ("firstWrite", Json.num s.firstWrite)
                      , ("firstBoundary", Json.num s.firstBoundary)
                      ]
                  IO.println (HeytingLean.Util.JCS.canonicalString out)
                  return 0

