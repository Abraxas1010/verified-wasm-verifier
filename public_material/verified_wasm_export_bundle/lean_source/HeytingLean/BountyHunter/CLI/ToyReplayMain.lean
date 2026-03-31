import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.AlgebraIR.Replay
import HeytingLean.BountyHunter.AlgebraIR.ToyEVMReplay

/-!
# `bounty_hunter_toy_replay_cli`

Executable that replays a `Replay.Trace` (typically emitted by `bounty_hunter_algebrair_cli --emit-replay`)
against a minimal toy EVM state (storage + boundary calls).

This is an executable checkpoint on the path to CoreEVM / Foundry replay.
-/

open IO

namespace HeytingLean.BountyHunter.CLI

private def eprintlnErr (msg : String) : IO Unit :=
  IO.eprintln msg

private def outputJson (j : Lean.Json) : IO Unit :=
  IO.println (HeytingLean.Util.JCS.canonicalString j)

private def findArgVal (args : List String) (k : String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | a :: b :: rest => if a = k then some b else go (b :: rest)
    | _ :: [] => none
  go args

private def hasFlag (args : List String) (k : String) : Bool :=
  args.any (· = k)

private def usage : String :=
  String.intercalate "\n"
    [ "usage:"
    , "  bounty_hunter_toy_replay_cli --input <verdict_or_trace.json> [--slot <n>]"
    , "  bounty_hunter_toy_replay_cli --stdin [--slot <n>]"
    , "  bounty_hunter_toy_replay_cli --selftest"
    , ""
    , "notes:"
    , "  - if the input JSON is a full verdict bundle, it must contain `replay`."
    ]

private def readFileE (path : System.FilePath) : IO (Except String String) := do
  try
    let s ← FS.readFile path
    pure (.ok s)
  catch e =>
    pure (.error s!"read error at {path}: {e}")

private def parseSlotFromWitness? (j : Lean.Json) : Option Nat :=
  match j.getObjVal? "witness" with
  | .ok w =>
      match w.getObjVal? "slot" with
      | .ok s =>
          match s.getNat? with
          | .ok n => some n
          | .error _ => none
      | .error _ => none
  | .error _ => none

private def parseReplayTraceE (j : Lean.Json) : Except String HeytingLean.BountyHunter.AlgebraIR.Replay.Trace := do
  match j.getObjVal? "replay" with
  | .ok r => HeytingLean.BountyHunter.AlgebraIR.Replay.traceFromJsonE r
  | .error _ => HeytingLean.BountyHunter.AlgebraIR.Replay.traceFromJsonE j

private def selftest : Except String Unit := do
  let mk (effects0 effects1 : Array HeytingLean.BountyHunter.AlgebraIR.Effect) :
      HeytingLean.BountyHunter.AlgebraIR.Replay.Trace :=
    { path :=
        #[ { node := 0, tag := "n0", effects := effects0 }
         , { node := 1, tag := "n1", effects := effects1 } ] }
  let slot := 0
  let tV := mk #[.boundaryCall "call"] #[.storageWrite slot]
  let tS := mk #[.storageWrite slot] #[.boundaryCall "call"]
  let rV := HeytingLean.BountyHunter.AlgebraIR.ToyEVMReplay.run slot tV
  let rS := HeytingLean.BountyHunter.AlgebraIR.ToyEVMReplay.run slot tS
  if !rV.verdict.startsWith "VULNERABLE" then
    throw s!"toy replay expected VULNERABLE, got {rV.verdict}"
  if !rS.verdict.startsWith "SAFE" then
    throw s!"toy replay expected SAFE, got {rS.verdict}"
  let j := HeytingLean.BountyHunter.AlgebraIR.Replay.traceToJson tV
  let t2 ← HeytingLean.BountyHunter.AlgebraIR.Replay.traceFromJsonE j
  if t2 ≠ tV then
    throw "trace roundtrip failed"
  pure ()

def runWithArgs (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  if args.isEmpty || hasFlag args "--help" || hasFlag args "-h" then
    IO.println usage
    return 0

  if hasFlag args "--selftest" then
    match selftest with
    | .ok () =>
        IO.println "OK"
        return 0
    | .error e =>
        eprintlnErr e
        return 1

  let slotOpt :=
    match findArgVal args "--slot" with
    | some s => s.toNat?
    | none => none

  let raw ←
    if hasFlag args "--stdin" then
      pure (.ok (← (← IO.getStdin).readToEnd))
    else
      match findArgVal args "--input" with
      | none => pure (.error "missing --input (or use --stdin)")
      | some p => readFileE p

  let raw ←
    match raw with
    | .ok s => pure s
    | .error e =>
        eprintlnErr e
        IO.println usage
        return 1

  let j ←
    match Lean.Json.parse raw with
    | .ok j => pure j
    | .error e =>
        eprintlnErr s!"JSON parse error: {e}"
        return 1

  let slot :=
    match slotOpt with
    | some s => some s
    | none => parseSlotFromWitness? j

  match slot with
  | none =>
      eprintlnErr "missing --slot <nat> (and no witness.slot present)"
      return 1
  | some slot =>
      match parseReplayTraceE j with
      | .error e =>
          eprintlnErr e
          return 1
      | .ok t =>
          let r := HeytingLean.BountyHunter.AlgebraIR.ToyEVMReplay.run slot t
          outputJson (HeytingLean.BountyHunter.AlgebraIR.ToyEVMReplay.reportToJson r)
          return 0

end HeytingLean.BountyHunter.CLI

def main (args : List String) : IO UInt32 :=
  HeytingLean.BountyHunter.CLI.runWithArgs args
