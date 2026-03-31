import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.ProofGraph.Extract
import HeytingLean.ProofGraph.Compat.ProofGraphDump
import HeytingLean.ProofGraph.VerifierWitness

open Lean

namespace HeytingLean.CLI.ProofGraphExtract

open HeytingLean.ProofGraph

structure Args where
  constName : Option String := none
  extraModules : List String := []
  fuel : Nat := 4096
  compatDump : Bool := false
  verifierBenchmark? : Option String := none
  deriving Inhabited

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

private def parseArgs (argv : List String) : Args :=
  let argv := HeytingLean.CLI.stripLakeArgs argv
  let constName := parseArg argv "--const"
  let extraModules := parseArgsMany argv "--module"
  let fuel := (parseArg argv "--fuel").bind String.toNat? |>.getD 4096
  let compatDump := argv.any (· == "--compat-dump")
  let verifierBenchmark? := parseArg argv "--verifier-benchmark"
  { constName, extraModules, fuel, compatDump, verifierBenchmark? }

private def usage : String :=
  String.intercalate "\n"
    [ "proof_graph_extract"
    , ""
    , "Export the canonical Heyting proof graph for a declaration."
    , ""
    , "Usage:"
    , "  lake exe proof_graph_extract -- --const HeytingLean.LoF.MRSystems.closedSelectorNucleus_fixed_iff"
    , ""
    , "Options:"
    , "  --const <Name>     constant to inspect (required)"
    , "  --module <M>       extra module(s) to import (repeatable)"
    , "  --fuel <n>         recursion fuel for expression traversal (default: 4096)"
    , "  --compat-dump      emit legacy proof_graph_dump-compatible JSON"
    , "  --verifier-benchmark <path>  attach verifier witnesses from a retained benchmark artifact"
    ]

def main (argv : List String) : IO UInt32 := do
  let args := parseArgs argv
  let some constName := args.constName
    | IO.eprintln usage; return 1
  let env ← importProject args.extraModules (constName? := some constName)
  let some declName := findConst env constName
    | IO.eprintln s!"constant not found: {constName}"; return 1
  let some ci := env.find? declName
    | IO.eprintln s!"constant info unavailable: {constName}"; return 1
  let graph0 := extractGraph declName ci args.fuel
  let graph ←
    match args.verifierBenchmark? with
    | some p =>
        match ← attachBenchmarkArtifact graph0 (System.FilePath.mk p) with
        | .ok g => pure g
        | .error e => IO.eprintln e; return 1
    | none => pure graph0
  let payload :=
    if args.compatDump then
      HeytingLean.ProofGraph.Compat.toLegacyDumpJson graph
    else
      graph.asJson
  IO.println (toString payload)
  return 0

end HeytingLean.CLI.ProofGraphExtract

open HeytingLean.CLI.ProofGraphExtract in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ProofGraphExtract.main args
