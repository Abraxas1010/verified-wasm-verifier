import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.Solc.YulTextMini
import HeytingLean.BountyHunter.AlgebraIR.CEI

/-!
# `yultextmini_cei_check`

Small executable for:
- parsing a Yul-text snippet (restricted `YulTextMini` subset),
- translating to `AlgebraIR`,
- running the CEI/dominance check on a concrete slot,
- emitting deterministic JSON.

This is intended as a minimal “semantic spine” check:
if this tool can parse + build CFG + produce expected CEI verdicts for
representative snippets, we have higher confidence that the BH pipeline’s
Yul ingestion is behaving as intended.
-/

open IO
open Lean
open HeytingLean.BountyHunter.Solc.YulTextMini
open HeytingLean.BountyHunter.AlgebraIR

private def usage : String :=
  String.intercalate "\n"
    [ "usage:"
    , "  yultextmini_cei_check --selftest"
    , "  yultextmini_cei_check --input <path.yul> --func <name> --slot <n>"
    , ""
    , "notes:"
    , "- This parses a *restricted* Yul-text subset (enough for Phase 0 effects)."
    , "- `--selftest` runs two built-in snippets (safe vs vulnerable ordering)."
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

private def mkResultJson
    (label : String)
    (verdict : Verdict)
    (w? : Option CEIWitness)
    (graph : Graph)
    (fnName : String)
    : Json :=
  Json.mkObj
    [ ("label", Json.str label)
    , ("function", Json.str fnName)
    , ("graphEntry", Json.num graph.entry)
    , ("graphNodes", Json.num graph.nodes.size)
    , ("verdictBundle", verdictBundleToJson verdict w?)
    ]

private def runOnSrcE (label : String) (src : String) (fnName : String) (slot : Nat) :
    Except String Json := do
  let body ← parseFunctionBodyE src fnName
  let g := toAlgebraIR body
  let (v, w?) := checkCEI g slot
  pure (mkResultJson label v w? g fnName)

private def selftestSrcSafe : String :=
  String.intercalate "\n"
    [ "function f() {"
    , "  sstore(0, 1)"
    , "  pop(call(gas(), 0, 0, 0, 0, 0, 0))"
    , "}"
    ]

private def selftestSrcVuln : String :=
  String.intercalate "\n"
    [ "function f() {"
    , "  pop(call(gas(), 0, 0, 0, 0, 0, 0))"
    , "  sstore(0, 1)"
    , "}"
    ]

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  if args.isEmpty || hasFlag "--help" args || hasFlag "-h" args then
    IO.println usage
    return 0
  if hasFlag "--selftest" args then
    match runOnSrcE "safe" selftestSrcSafe "f" 0, runOnSrcE "vuln" selftestSrcVuln "f" 0 with
    | .ok j1, .ok j2 =>
        let out := Json.mkObj [("version", Json.str "yultextmini_cei_check.v0"), ("results", Json.arr #[j1, j2])]
        IO.println (HeytingLean.Util.JCS.canonicalString out)
        return 0
    | .error e, _ =>
        IO.eprintln s!"selftest failed: {e}"
        return 1
    | _, .error e =>
        IO.eprintln s!"selftest failed: {e}"
        return 1
  let inPath? := getArgValue? "--input" args
  let fnName := (getArgValue? "--func" args).getD "f"
  let slotStr? := getArgValue? "--slot" args
  match inPath?, slotStr? with
  | some inPath, some slotStr =>
      match slotStr.toNat? with
      | none =>
          IO.eprintln s!"invalid --slot {slotStr}"
          return 1
      | some slot =>
          match (← readFileE (System.FilePath.mk inPath)) with
          | .error e =>
              IO.eprintln e
              return 1
          | .ok src =>
              match runOnSrcE "file" src fnName slot with
              | .error e =>
                  IO.eprintln e
                  return 1
              | .ok outJson =>
                  IO.println (HeytingLean.Util.JCS.canonicalString outJson)
                  return 0
  | _, _ =>
      IO.eprintln usage
      return 1
