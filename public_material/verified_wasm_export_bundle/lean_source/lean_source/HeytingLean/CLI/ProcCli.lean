import Lean
import HeytingLean.PCC.API
import HeytingLean.CLI.Args

open System
open Lean
open HeytingLean.PCC

namespace HeytingLean.CLI
namespace ProcCli

private def usage : String :=
  String.intercalate "\n"
    [ "proc_cli --list"
    , "proc_cli --run <procId> '<json-state>'"
    , ""
    , "Examples:"
    , "  proc_cli --run add1 '{\"args\":[0]}'"
    , "  proc_cli --run add2 '{\"args\":[1,2]}'"
    , "  proc_cli --run max2 '{\"args\":[3,4]}'"
    , "  proc_cli --run xorSum '{\"args\":[3,4]}'"
    ]

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | ["--list"] =>
      let js ← apiListProcesses
      IO.println js.pretty
      pure 0
  | ["--run", pid, jsonStr] =>
      match Json.parse jsonStr with
      | Except.error e =>
          IO.eprintln s!"JSON parse error: {e}"
          pure 1
      | Except.ok j =>
          -- Normalise the payload so Exec can decode args easily.
          let payload : Json :=
            match j with
            | Json.obj _ => j
            | Json.arr _ => Json.mkObj [("args", j)]
            | other      => Json.mkObj [("args", Json.arr #[other])]
          let req :=
            Json.mkObj [("proc", Json.str pid), ("state", payload)]
          try
            let out ← apiRunProcess req
            IO.println out.pretty
            pure 0
          catch e =>
            IO.eprintln s!"run error: {e.toString}"
            pure 1
  | _ =>
      IO.eprintln usage
      pure 1

end ProcCli
end HeytingLean.CLI

/-- Expose entry point for Lake. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ProcCli.main args
