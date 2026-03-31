import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Trace

open Lean

namespace HeytingLean.CLI
namespace TraceDigest

def run : IO Unit := do
  match (← IO.getEnv "LOF_TRACE_PATH") with
  | none => do
      IO.eprintln "LOF_TRACE_PATH not set"
      IO.Process.exit 1
  | some p =>
      let fp := System.FilePath.mk p
      let content? ← (do
        try
          if ← fp.pathExists then return some (← IO.FS.readFile fp) else return none
        catch _ => return none)
      match content? with
      | none =>
          IO.eprintln s!"trace file not found: {p}"
          IO.Process.exit 1
      | some s =>
          match Json.parse s with
          | .error _ =>
              IO.eprintln "invalid trace JSON"
              IO.Process.exit 1
          | .ok j =>
              match HeytingLean.Crypto.Trace.parseOpsJson j with
              | none =>
                  IO.eprintln "invalid trace ops"
                  IO.Process.exit 1
              | some ops =>
                  let d := HeytingLean.Crypto.Trace.digestOps ops
                  IO.println (Json.mkObj [("trace_digest", Json.str (toString d))] |>.compress)

end TraceDigest
end HeytingLean.CLI

def main : IO Unit := HeytingLean.CLI.TraceDigest.run

