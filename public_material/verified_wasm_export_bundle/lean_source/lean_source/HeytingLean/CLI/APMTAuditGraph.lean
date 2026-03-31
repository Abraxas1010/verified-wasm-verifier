import Lean
import Lean.Data.Json
import HeytingLean.Boundary.Digests
import HeytingLean.Policy.Recipients
import HeytingLean.Policy.Budget
import HeytingLean.Policy.Lineage
import HeytingLean.Policy.Refinement

open Lean
open System
open HeytingLean
open HeytingLean.Boundary.Digests
open HeytingLean.Policy
open HeytingLean.Policy.Lineage

namespace HeytingLean.CLI
namespace APMTAuditGraph

structure CliOpts where
  input    : Option FilePath := none
  stdin    : Bool := false
  failFast : Bool := false
deriving Inhabited

private def usage : String :=
  "apmt_audit_graph [--input <dag.json> | --stdin] [--fail-fast]"

def parseArgs : List String → Except String CliOpts
  | [] => return {}
  | "--input" :: path :: rest =>
      return { (← parseArgs rest) with input := some ⟨path⟩ }
  | "--stdin" :: rest =>
      return { (← parseArgs rest) with stdin := true }
  | "--fail-fast" :: rest =>
      return { (← parseArgs rest) with failFast := true }
  | flag :: _ => throw s!"unknown option: {flag}"

/-! ## Helpers -/

private def getField (j : Json) (name : String) : Except String Json :=
  j.getObjVal? name

private def getNat (j : Json) (name : String) : Except String Nat :=
  j.getObjValAs? Nat name

private def getString (j : Json) (name : String) : Except String String :=
  j.getObjValAs? String name

private def parseRecipient (j : Json) : Except String RecipientSpec := do
  let tag ← getString j "tag"
  match tag with
  | "all"      => pure .all
  | "verified" => pure .verified
  | "custom"   =>
      let ids ← match j.getObjValAs? (Array Nat) "ids" with
        | Except.ok arr  => pure arr.toList
        | Except.error _ => pure []
      pure (.custom ids)
  | other => .error s!"unknown recipient tag '{other}'"

private def parseCert (j : Json) : Except String Policy.Cert := do
  let recipients ← parseRecipient (← getField j "recipients")
  let budget ← getNat j "budget"
  let startTs ← getNat j "startTs"
  let endTs   ← getNat j "endTs"
  pure { recipients, budget, startTs, endTs }

private def parseStmt (j : Json) : Except String HeytingLean.Boundary.Digests.StmtInputs := do
  let parent ← getString j "parent"
  let toAddr ← getNat j "toAddr"
  let vendor ← getNat j "vendor"
  let amount ← getNat j "amount"
  let now    ← getNat j "now"
  pure {
    parentReceiptHash := parent
    toAddr := toAddr
    vendor := vendor
    amount := amount
    now := now
  }

private def parseBudget (j : Json) : Except String (List Nat × Nat) := do
  let limit ← getNat j "limit"
  let amounts ← match j.getObjValAs? (Array Nat) "amounts" with
    | Except.ok arr  => pure arr.toList
    | Except.error _ => pure []
  pure (amounts, limit)

/-! ## Audit checks -/

private def auditEdges (dag : Json) (failFast : Bool) : Bool × Option Json :=
  match dag.getObjVal? "edges" with
  | .ok (.arr edges) =>
      let rec loop (idx : Nat) (items : List Json) (accOk : Bool) (fail? : Option Json) : Bool × Option Json :=
        match items with
        | [] => (accOk, fail?)
        | edge :: rest =>
            let ok := match (edge.getObjVal? "parent", edge.getObjVal? "child") with
              | (.ok (.str parent), .ok child) =>
                  match parseStmt child with
                  | Except.ok stmt   => Lineage.lineageOk parent stmt
                  | Except.error _   => false
              | _ => false
            let fail? := if !ok && fail?.isNone then
                some (Json.mkObj [("type", Json.str "lineage"), ("edge", toJson idx)])
              else fail?
            let accOk := accOk && ok
            if failFast && !ok then
              (accOk, fail?)
            else
              loop (idx + 1) rest accOk fail?
      loop 0 edges.toList true none
  | _ => (true, none)

private def auditBudget (dag : Json) : Bool × Option Json :=
  match dag.getObjVal? "budgets" with
  | .ok obj =>
      match parseBudget obj with
      | Except.ok (amounts, limit) =>
          let ok := Policy.budgetOk amounts limit
          (ok, if ok then none else some (Json.mkObj [("type", Json.str "budget"), ("limit", toJson limit)]))
      | Except.error _ => (false, some (Json.mkObj [("type", Json.str "budget"), ("reason", Json.str "parse")]))
  | .error _ => (true, none)

private def auditRecipients (dag : Json) : Bool × Option Json :=
  match (dag.getObjVal? "parentCert", dag.getObjVal? "childCert") with
  | (.ok parentJ, .ok childJ) =>
      match (parseCert parentJ, parseCert childJ) with
      | (Except.ok parentC, Except.ok childC) =>
          let ok := recipientRefines parentC.recipients childC.recipients
          (ok, if ok then none else some (Json.mkObj [("type", Json.str "recipient")]))
      | _ => (false, some (Json.mkObj [("type", Json.str "recipient"), ("reason", Json.str "parse")]))
  | _ => (true, none)

private def auditRefinement (dag : Json) : Bool × Option Json :=
  match (dag.getObjVal? "parentCert", dag.getObjVal? "childCert") with
  | (.ok parentJ, .ok childJ) =>
      match (parseCert parentJ, parseCert childJ) with
      | (Except.ok parentC, Except.ok childC) =>
          let ok := Policy.refines parentC childC
          (ok, if ok then none else some (Json.mkObj [("type", Json.str "refinement")]))
      | _ => (false, some (Json.mkObj [("type", Json.str "refinement"), ("reason", Json.str "parse")]))
  | _ => (true, none)

/-! ## Sample DAG -/

private def sampleDag : Json :=
  Json.mkObj [
    ("edges", toJson
      [ Json.mkObj [
          ("parent", Json.str "ps:PARENT:deadbeef"),
          ("child", Json.mkObj [
            ("parent", Json.str "ps:PARENT:deadbeef"),
            ("toAddr", toJson 1),
            ("vendor", toJson 2),
            ("amount", toJson 5),
            ("now", toJson 0)
          ])
        ]
      ]),
    ("budgets", Json.mkObj [
      ("limit", toJson 10),
      ("amounts", toJson ([5, 4, 1] : List Nat))
    ]),
    ("parentCert", Json.mkObj [
      ("recipients", Json.mkObj [("tag", Json.str "custom"), ("ids", toJson ([0,1,2] : List Nat))]),
      ("budget", toJson 100),
      ("startTs", toJson 0),
      ("endTs", toJson 1000)
    ]),
    ("childCert", Json.mkObj [
      ("recipients", Json.mkObj [("tag", Json.str "custom"), ("ids", toJson ([1,2] : List Nat))]),
      ("budget", toJson 10),
      ("startTs", toJson 10),
      ("endTs", toJson 100)
    ])
  ]

/-! ## CLI entry -/

private def loadDag (opts : CliOpts) : IO Json := do
  if opts.stdin then
    match Json.parse (← (← IO.getStdin).readToEnd) with
    | .ok j      => pure j
    | .error err => throw <| IO.userError s!"JSON parse error: {err}"
  else if let some fp := opts.input then
    match Json.parse (← IO.FS.readFile fp) with
    | .ok j      => pure j
    | .error err => throw <| IO.userError s!"JSON parse error: {err}"
  else
    pure sampleDag

private def evalDag (dag : Json) (failFast : Bool) : Json × UInt32 :=
  let (edgesOk, edgeFail) := auditEdges dag failFast
  let (budgetOk, budgetFail) := auditBudget dag
  let (recipOk, recipFail) := auditRecipients dag
  let (refineOk, refineFail) := auditRefinement dag

  let failure :=
    match edgeFail with
    | some f => some f
    | none =>
      match budgetFail with
      | some f => some f
      | none =>
        match recipFail with
        | some f => some f
        | none => refineFail

  let ok := edgesOk && budgetOk && recipOk && refineOk
  let base : List (String × Json) := [
    ("ok", Json.bool ok),
    ("edges_ok", Json.bool edgesOk),
    ("budget_ok", Json.bool budgetOk),
    ("recipient_refines_ok", Json.bool recipOk),
    ("refines_ok", Json.bool refineOk)
  ]
  let extra := match failure with
    | some fail => [("failure", fail)]
    | none      => []
  (Json.mkObj (base ++ extra), if ok then 0 else 1)

def runWithArgs (argv : List String) : IO UInt32 := do
  if argv.any (· = "--help") || argv.any (· = "-h") then
    IO.println usage
    return 0
  match parseArgs argv with
  | Except.error msg =>
      IO.eprintln s!"argument error: {msg}"
      IO.eprintln usage
      return 2
  | Except.ok opts =>
      try
        let dag ← loadDag opts
        let (json, code) := evalDag dag opts.failFast
        IO.println json.compress
        return code
      catch err =>
        IO.eprintln err.toString
        return 1

end APMTAuditGraph
end HeytingLean.CLI
