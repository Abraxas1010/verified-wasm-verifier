import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.R1CSBoolEnv
import HeytingLean.Payments.Types
import HeytingLean.Payments.Rules
import HeytingLean.Payments.Types
import HeytingLean.CLI.Args

/-!
Emit an explainer JSON for the Payments policy flow:
 - Form (Form 4) AST in a JSON-friendly shape
 - Compiled program (postfix instructions) as strings
 - VM trace (BoolLens) stack snapshots
 - R1CS meta: output_index and env_indices (via env→var map)
 - Counts: constraints, maxVar
This is used by the interactive demo to visualize the pipeline.
-/

namespace HeytingLean
namespace Payments
namespace CLI
namespace PMExplain

open IO
open Lean
open Crypto
open Crypto.BoolLens

private def readFileE (path : System.FilePath) : IO (Except String String) := do
  try let s ← FS.readFile path; pure (.ok s) catch e => pure (.error s!"read error at {path}: {e}")

private def parseJsonE (raw : String) : Except String Json :=
  match Json.parse raw with | .ok j => .ok j | .error e => .error e

/- Boolean formula over 4 variables: a ∧ b ∧ c ∧ d -/
def policyFormula4 : Crypto.Form 4 :=
  let v (i : Fin 4) := Crypto.Form.var i
  let a : Crypto.Form 4 := v ⟨0, by decide⟩
  let b : Crypto.Form 4 := v ⟨1, by decide⟩
  let c : Crypto.Form 4 := v ⟨2, by decide⟩
  let d : Crypto.Form 4 := v ⟨3, by decide⟩
  Crypto.Form.and (Crypto.Form.and a b) (Crypto.Form.and c d)

/- Build Env 4 from flags in order: [allowedRecipient, amountOkPerTx, perWindowOk, budgetOk] -/
def env4 (f0 f1 f2 f3 : Bool) : BoolLens.Env 4 := fun i =>
  match i.1 with
  | 0 => f0
  | 1 => f1
  | 2 => f2
  | 3 => f3
  | _ => false

/- Render Form 4 to a compact JSON-friendly AST used by the UI. -/
inductive FormJ where
  | top | bot | var (idx : Nat)
  | and (lhs rhs : FormJ)
  | or (lhs rhs : FormJ)
  | imp (lhs rhs : FormJ)
  deriving Repr

namespace FormJ

open HeytingLean.Crypto (Form)

def ofForm4 : Form 4 → FormJ
  | .top => .top
  | .bot => .bot
  | .var i => .var i.1
  | .and a b => .and (ofForm4 a) (ofForm4 b)
  | .or a b  => .or  (ofForm4 a) (ofForm4 b)
  | .imp a b => .imp (ofForm4 a) (ofForm4 b)

open Lean (Json)

def toJson : FormJ → Json
  | .top => Json.mkObj [("tag", Json.str "top")]
  | .bot => Json.mkObj [("tag", Json.str "bot")]
  | .var i => Json.mkObj [("tag", Json.str "var"), ("idx", Json.num i)]
  | .and l r => Json.mkObj [("tag", Json.str "and"), ("lhs", toJson l), ("rhs", toJson r)]
  | .or  l r => Json.mkObj [("tag", Json.str "or"),  ("lhs", toJson l), ("rhs", toJson r)]
  | .imp l r => Json.mkObj [("tag", Json.str "imp"), ("lhs", toJson l), ("rhs", toJson r)]

end FormJ

/- Convert a compiled program to a human-readable string list. -/
def programToStrings {n} : Crypto.Program n → List String
  | [] => []
  | instr :: rest =>
      let s := match instr with
        | .pushTop => "pushTop"
        | .pushBot => "pushBot"
        | .pushVar i => s!"pushVar({i.1})"
        | .applyAnd => "applyAnd"
        | .applyOr  => "applyOr"
        | .applyImp => "applyImp"
      s :: programToStrings rest

/- Convert BoolLens trace (list of stacks) into JSON arrays of booleans. -/
def traceToJson (tr : BoolLens.Trace) : Json :=
  let arr := tr.map (fun stk => Json.arr (stk.map (fun b => Json.bool b)).toArray)
  Json.arr arr.toArray

open Lean (Json)

def jsonOfListStr (xs : List String) : Json :=
  Json.arr (xs.map (fun s => Json.str s)).toArray

/- Compute max variable index referenced in a system. -/
def maxVarInSystem (sys : HeytingLean.Crypto.ZK.System) : Nat :=
  let step := fun acc (ts : List (Crypto.ZK.Var × ℚ)) => ts.foldl (fun a p => Nat.max a p.fst) acc
  sys.constraints.foldl (init := 0) (fun m c =>
    let m1 := step 0 c.A.terms
    let m2 := step m1 c.B.terms
    let m3 := step m2 c.C.terms
    Nat.max m m3)

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | [policyPath, statePath, requestPath] =>
      -- Load JSON inputs
      let polRaw ← match (← readFileE (System.FilePath.mk policyPath)) with | .ok s => pure s | .error e => eprintln e; return 1
      let stRaw  ← match (← readFileE (System.FilePath.mk statePath)) with  | .ok s => pure s | .error e => eprintln e; return 1
      let rqRaw  ← match (← readFileE (System.FilePath.mk requestPath)) with | .ok s => pure s | .error e => eprintln e; return 1
      let polJ ← match parseJsonE polRaw with | .ok j => pure j | .error e => eprintln e; return 1
      let stJ  ← match parseJsonE stRaw  with | .ok j => pure j | .error e => eprintln e; return 1
      let rqJ  ← match parseJsonE rqRaw  with | .ok j => pure j | .error e => eprintln e; return 1
      -- Decode domain
      let pol ← match Payments.JsonCodec.parsePolicy polJ with | .ok p => pure p | .error e => eprintln e; return 1
      let st  ← match Payments.JsonCodec.parseState stJ with  | .ok s => pure s | .error e => eprintln e; return 1
      let req ← match Payments.JsonCodec.parseRequest rqJ with | .ok r => pure r | .error e => eprintln e; return 1
      -- Compute checks and env
      let checks := Payments.Rules.computeChecks pol st req
      let st' := Payments.Rules.applyRequest pol st req
      let decision := checks.allowedRecipient && checks.amountOkPerTx && checks.perWindowOk && checks.budgetOk
      let ρ : BoolLens.Env 4 := env4 checks.allowedRecipient checks.amountOkPerTx checks.perWindowOk checks.budgetOk
      let φ := policyFormula4
      -- Build program/trace
      let prog := Crypto.Form.compile φ
      let trace := BoolLens.traceFrom ρ prog []
      -- Compile to R1CS and extract env map
      let compiledWithMap := Crypto.ZK.R1CSBoolEnv.compileWithEnvMap φ ρ
      let compiled := compiledWithMap.fst
      let envMap := compiledWithMap.snd -- list of (envIdx, var)
      -- Build env_indices by taking first var per env 0..3
      let idxFor (i : Nat) : Nat :=
        match envMap.find? (fun p => p.fst = i) with
        | some p => p.snd
        | none => 0
      let envIdxs : List Nat := [idxFor 0, idxFor 1, idxFor 2, idxFor 3]
      let maxVar := maxVarInSystem compiled.system
      let counts := Json.mkObj [("constraints", Json.num compiled.system.constraints.length), ("maxVar", Json.num maxVar)]
      let metaJ := Json.mkObj [ ("output_index", Json.num compiled.output)
                              , ("env_indices", Json.arr (envIdxs.map (fun n => Json.num n)).toArray) ]
      -- Human-friendly checks explanation
      let checksJ := Json.mkObj
        [ ("allowedRecipient", Json.bool checks.allowedRecipient)
        , ("amountOkPerTx", Json.bool checks.amountOkPerTx)
        , ("perWindowOk", Json.bool checks.perWindowOk)
        , ("budgetOk", Json.bool checks.budgetOk)
        , ("decision", Json.bool decision)
        ]

      -- Canonical JSONs (for transparency in the UI)
      let policyCanon := (Payments.JsonCodec.policyToCanonicalJson pol)
      let stateCanon  := (Payments.JsonCodec.stateToCanonicalJson st)
      let statePostCanon := (Payments.JsonCodec.stateToCanonicalJson st')

      let out := Json.mkObj
        [ ("form", FormJ.toJson (FormJ.ofForm4 φ))
        , ("program", jsonOfListStr (programToStrings prog))
        , ("vmTrace", traceToJson trace)
        , ("meta", metaJ)
        , ("envMap", Json.arr (envMap.map (fun p => Json.mkObj [("env", Json.num p.fst), ("var", Json.num p.snd)])).toArray)
        , ("counts", counts)
        , ("policyCanonical", policyCanon)
        , ("stateCanonical", stateCanon)
        , ("statePostCanonical", statePostCanon)
        , ("checks", checksJ)
        ]
      println out.compress
      return 0
  | _ =>
      eprintln "Usage: lake exe pm_explain <policy.json> <state.json> <request.json>"
      return 1

end PMExplain
end CLI
end Payments
end HeytingLean

-- Linker alias
open HeytingLean.Payments.CLI.PMExplain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Payments.CLI.PMExplain.main args
