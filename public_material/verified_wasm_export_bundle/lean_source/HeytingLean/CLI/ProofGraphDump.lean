import Lean
import HeytingLean.CLI.Args
import HeytingLean.ProofGraph.Extract
import HeytingLean.ProofGraph.Compat.ProofGraphDump

/-
Compatibility frontend preserving the historic `proof_graph_dump` command while
delegating to the canonical `proof_graph_extract` pipeline.
-/
open Lean
open HeytingLean.ProofGraph

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest => if x == flag then some y else parseArg (y :: rest) flag
  | _ => none

private def parseArgsMany (args : List String) (flag : String) : List String :=
  match args with
  | [] => []
  | x :: y :: rest =>
      if x = flag then
        y :: parseArgsMany rest flag
      else
        parseArgsMany (y :: rest) flag
  | _ => []

def main (argv : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  let some constName := parseArg argv "--const"
    | IO.println (toString <| Json.mkObj [("nodes", Json.arr #[]), ("edges", Json.arr #[]), ("root", Json.num 0)]); return 1
  let extraModules := parseArgsMany argv "--module"
  let fuel := (parseArg argv "--fuel").bind String.toNat? |>.getD 4096
  let env ← importProject extraModules
  let some declName := findConst env constName
    | IO.println (toString <| Json.mkObj [("nodes", Json.arr #[]), ("edges", Json.arr #[]), ("root", Json.num 0)]); return 1
  let some ci := env.find? declName
    | IO.println (toString <| Json.mkObj [("nodes", Json.arr #[]), ("edges", Json.arr #[]), ("root", Json.num 0)]); return 1
  let graph := extractGraph declName ci fuel
  IO.println (toString <| Compat.toLegacyDumpJson graph)
  return 0
