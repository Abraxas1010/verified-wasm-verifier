import Lean
import Lean.Data.Json
import HeytingLean.Boundary.Digests
import HeytingLean.Policy.Recipients
import HeytingLean.Policy.Budget
import HeytingLean.Policy.Lineage
import HeytingLean.Policy.Refinement
import HeytingLean.Theorems.Core
import HeytingLean.Theorems.Cert
import HeytingLean.Exec.Registry
import HeytingLean.Theorems.Cert

namespace HeytingLean
namespace PCC

open Lean
open HeytingLean.Boundary
open HeytingLean.Policy
open HeytingLean.Theorems

/-! ## JSON helpers -/

private def expectField (j : Json) (name : String) : Except String Json :=
  j.getObjVal? name

private def expectNat (j : Json) (name : String) : Except String Nat :=
  j.getObjValAs? Nat name

private def expectString (j : Json) (name : String) : Except String String :=
  j.getObjValAs? String name

def loadTheoremManifest (path : System.FilePath) : IO Json := do
  if !(← path.pathExists) then
    throw <| IO.userError s!"theorems manifest not found at {path}"
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | Except.ok j => pure j
  | Except.error e => throw <| IO.userError s!"failed to parse theorems manifest at {path}: {e}"

private def filterManifestTheorems (j : Json) (cat? kind? : Option String) : Json := Id.run do
  match j.getObjVal? "theorems" with
  | Except.ok (Json.arr arr) =>
      let filtered := arr.filter (fun t =>
        let catOk := match cat? with
          | none => true
          | some c => match t.getObjValAs? String "category" with
            | .ok v => v == c
            | _ => false
        let kindOk := match kind? with
          | none => true
          | some k => match t.getObjValAs? String "kind" with
            | .ok v => v == k
            | _ => false
        catOk && kindOk)
      Json.arr filtered
  | _ => Json.arr #[]

private def manifestLookup (j : Json) (nm : String) : Json := Id.run do
  match j.getObjVal? "theorems" with
  | Except.ok (Json.arr arr) =>
      match arr.find? (fun t =>
        match t.getObjValAs? String "name" with
        | .ok v => v == nm
        | _ => false) with
      | some t => t
      | none => Json.null
  | _ => Json.null

private def optString (j : Json) (name : String) : Option String :=
  match j.getObjValAs? String name with
  | .ok s    => some s
  | .error _ => none

/-! ## Parsing -/

private def parseRecipient (j : Json) : Except String RecipientSpec := do
  let tag ← expectString j "tag"
  match tag with
  | "all"      => pure .all
  | "verified" => pure .verified
  | "custom"   =>
      let ids ← match j.getObjValAs? (Array Nat) "ids" with
        | Except.ok arr   => pure arr.toList
        | Except.error _  => pure []
      pure (.custom ids)
  | other => .error s!"unknown recipient tag '{other}'"

private def parseCert (j : Json) : Except String Policy.Cert := do
  let recipients ← parseRecipient (← expectField j "recipients")
  let budget     ← expectNat j "budget"
  let startTs    ← expectNat j "startTs"
  let endTs      ← expectNat j "endTs"
  pure {
    recipients := recipients
    budget := budget
    startTs := startTs
    endTs := endTs
  }

private def parseStmtInputs (j : Json) : Except String Digests.StmtInputs := do
  let parent ← expectString j "parent"
  let toAddr ← expectNat j "toAddr"
  let vendor ← expectNat j "vendor"
  let amount ← expectNat j "amount"
  let now    ← expectNat j "now"
  pure {
    parentReceiptHash := parent
    toAddr := toAddr
    vendor := vendor
    amount := amount
    now := now
  }

private def parseBudget (j : Json) : Except String (List Nat × Nat) := do
  let limit ← expectNat j "limit"
  let amountsJson ← j.getObjValAs? (Array Nat) "amounts"
  pure (amountsJson.toList, limit)

/-- Parse a dotted theorem name into a structured `Name`. Empty segments are ignored. -/
private def parseThmName (nm : String) : Name :=
  nm.splitOn "." |>.foldl (fun acc part =>
    if part.isEmpty then acc else Name.str acc part) Name.anonymous

/-! ## Sample data & encoders -/

structure Sample where
  policy : String
  stmt : Digests.StmtInputs
  parentRecip : RecipientSpec
  childRecip : RecipientSpec
  parentCert : Policy.Cert
  childCert : Policy.Cert
  amounts : List Nat
  limit : Nat

private def sampleData : Sample :=
  let policy := "{\"demo\":true,\"rules\":[1,2,3]}"
  let parent := "ps:PARENT:deadbeef"
  let stmt : Digests.StmtInputs := {
    parentReceiptHash := parent
    toAddr := 1
    vendor := 2
    amount := 10
    now := 123
  }
  let parentRecip : RecipientSpec := .custom [0, 1, 2, 3]
  let childRecip  : RecipientSpec := .custom [1, 2]
  let parentCert : Policy.Cert := {
    recipients := parentRecip
    budget := 100
    startTs := 0
    endTs := 1000
  }
  let childCert : Policy.Cert := {
    recipients := childRecip
    budget := 10
    startTs := 10
    endTs := 100
  }
  {
    policy := policy
    stmt := stmt
    parentRecip := parentRecip
    childRecip := childRecip
    parentCert := parentCert
    childCert := childCert
    amounts := [3, 4, 2]
    limit := 10
  }

def sampleRequest : Json :=
  Json.mkObj [("command", Json.str "selftest")]

private def recipientToJson : RecipientSpec → Json
  | .all        => Json.mkObj [("tag", Json.str "all")]
  | .verified   => Json.mkObj [("tag", Json.str "verified")]
  | .custom ids => Json.mkObj [("tag", Json.str "custom"), ("ids", toJson ids)]

private def certToJson (c : Policy.Cert) : Json :=
  Json.mkObj [
    ("recipients", recipientToJson c.recipients),
    ("budget", toJson c.budget),
    ("startTs", toJson c.startTs),
    ("endTs", toJson c.endTs)
  ]

private def stmtToJson (s : Digests.StmtInputs) : Json :=
  Json.mkObj [
    ("parent", Json.str s.parentReceiptHash),
    ("toAddr", toJson s.toAddr),
    ("vendor", toJson s.vendor),
    ("amount", toJson s.amount),
    ("now", toJson s.now)
  ]

private def selftestResponse (s : Sample) : Json :=
  Json.mkObj [
    ("canon",     Json.str (Digests.canonDigest s.policy)),
    ("stmtHash",  Json.str (Digests.stmtHash s.stmt)),
    ("lineage_ok", toJson (Lineage.lineageOk s.stmt.parentReceiptHash s.stmt)),
    ("recipient_refines_ok", toJson (Policy.recipientRefines s.parentRecip s.childRecip)),
    ("budget_ok", toJson (Policy.budgetOk s.amounts s.limit)),
    ("refines_ok", toJson (Policy.refines s.parentCert s.childCert))
  ]

/-- Compact summary of a tagged theorem block. -/
structure ThmSummary where
  name      : String
  typeStr   : String
  tags      : List String
  category  : String
  kind      : String
  deriving Repr, Lean.ToJson

/-- Certified theorem summary exposed via PCC. -/
abbrev CertifiedThmSummary := HeytingLean.Theorems.CertifiedThmSummary

/-- Summary of an executable process tied to a theorem. -/
structure ProcSummary where
  id      : String
  arity   : String
  specThm : String
  notes   : Option String
  deriving Repr, Lean.ToJson

private def summarizeThm (b : ThmBlock) : ThmSummary :=
  { name := toString b.id.name
    typeStr := b.typeStr
    tags := b.tags.namespaceHint ++ b.tags.lensHint
    category := b.category
    kind := HeytingLean.Theorems.kindToString b.kind }

private def summarizeCertified (ct : CertifiedThm) : CertifiedThmSummary :=
  HeytingLean.Theorems.toSummary ct

private def summarizeProc (p : Exec.Proc) : ProcSummary :=
  { id := p.id
    arity := Exec.arityToString p.arity
    specThm := toString p.spec.specThm.name
    notes := p.spec.notes }

private def filterThms (cat? kind? : Option String) (arr : Array ThmBlock) : Array ThmBlock :=
  arr.filter (fun b =>
    (match cat? with
     | none => true
     | some c => b.category == c) &&
    (match kind? with
     | none => true
     | some k => b.kind == k))

private def listTheoremsJson (cat? kind? : Option String) : Json :=
  let summaries := filterThms cat? kind? HeytingLean.Theorems.allThmBlocks |>.map summarizeThm
  toJson summaries

private def getTheoremJson (nm : String) : Json :=
  match HeytingLean.Theorems.findThmByName (parseThmName nm) with
  | some b => toJson (summarizeThm b)
  | none   => Json.null

/-! ## Dispatcher -/

private def mkOk (payload : Json) : Json :=
  Json.mkObj [("ok", Json.bool true), ("result", payload)]

private def mkErr (msg : String) (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([
    ("ok", Json.bool false),
    ("error", Json.str msg)
  ] ++ extra)

private def liftExcept {α} : Except String α → ExceptT String IO α
  | .ok a     => pure a
  | .error e  => ExceptT.mk (pure (.error e))

private def throwErr {α} (msg : String) : ExceptT String IO α :=
  ExceptT.mk (pure (.error msg))

/-- List all registered executable processes. -/
def apiListProcesses : IO Json := do
  let arr := Exec.allProcs.map summarizeProc
  pure (toJson arr)

/-- Run a process to fixed point given JSON payload `{proc: "...", state: {...}}`. -/
def apiRunProcess (req : Json) : IO Json := do
  let pid ←
    match expectString req "proc" with
    | .ok v => pure v
    | .error _ =>
        match expectString req "id" with
        | .ok v => pure v
        | .error e => throw <| IO.userError e
  let statePayload : Json ←
    match req.getObjVal? "state" with
    | .ok st => pure st
    | _ =>
        match req.getObjVal? "args" with
        | .ok (.arr arr) => pure <| Json.mkObj [("args", Json.arr arr)]
        | .ok _ => throw <| IO.userError "field 'args' must be an array"
        | _ => throw <| IO.userError "expected 'state' or 'args' field"
  match req with
  | Json.obj _ =>
    let some p := Exec.findProcById pid
      | throw <| IO.userError s!"unknown process id: {pid}"
    let s0 : Exec.State := { payload := statePayload }
    let (sFinal, converged) ← Exec.runToFixedPoint p s0
    pure <| Json.mkObj [
      ("proc",        Json.str pid),
      ("final_state", sFinal.payload),
      ("converged",   Json.bool converged)
    ]
  | _ =>
    throw <| IO.userError "expected JSON object for run_process request"

private def handleRequest (req : Json) : ExceptT String IO Json := do
  let cmd ← liftExcept <| expectString req "command"
  match cmd with
  | "canon_digest" =>
      let policy ← liftExcept <| expectString req "policyCanonical"
      return mkOk (Json.mkObj [("digest", Json.str (Digests.canonDigest policy))])
  | "stmt_hash" =>
      let stmtJ ← liftExcept <| expectField req "stmtInputs"
      let stmt ← liftExcept <| parseStmtInputs stmtJ
      return mkOk (Json.mkObj [("stmtHash", Json.str (Digests.stmtHash stmt))])
  | "recipient_refines" =>
      let parentJ ← liftExcept <| expectField req "parent"
      let childJ  ← liftExcept <| expectField req "child"
      let parent  ← liftExcept <| parseRecipient parentJ
      let child   ← liftExcept <| parseRecipient childJ
      return mkOk (Json.mkObj [("ok", toJson (Policy.recipientRefines parent child))])
  | "budget_ok" =>
      let (amounts, limit) ← liftExcept <| parseBudget req
      return mkOk (Json.mkObj [("ok", toJson (Policy.budgetOk amounts limit))])
  | "lineage_ok" =>
      let parent ← liftExcept <| expectString req "parent"
      let childJ ← liftExcept <| expectField req "child"
      let child  ← liftExcept <| parseStmtInputs childJ
      return mkOk (Json.mkObj [("ok", toJson (Lineage.lineageOk parent child))])
  | "cert_refines" =>
      let parentJ ← liftExcept <| expectField req "parentCert"
      let childJ  ← liftExcept <| expectField req "childCert"
      let parent  ← liftExcept <| parseCert parentJ
      let child   ← liftExcept <| parseCert childJ
      return mkOk (Json.mkObj [("ok", toJson (Policy.refines parent child))])
  | "selftest" =>
      return mkOk (Json.mkObj [
        ("request", sampleRequest),
        ("response", selftestResponse sampleData)
      ])
  | "list_theorems"
  | "list_certified_theorems" => do
      let cat? := optString req "category"
      let kind? := optString req "kind"
      -- Lightweight manifest-backed path to keep C embedding light: use on-disk manifest if available.
      let manifestPath := System.FilePath.mk ".." / HeytingLean.Theorems.manifestPath
      let useManifest ← System.FilePath.pathExists manifestPath
      if useManifest then
        let contents ← IO.FS.readFile manifestPath
        match Json.parse contents with
        | .ok j =>
            let filtered := filterManifestTheorems j cat? kind?
            return mkOk (Json.mkObj [("theorems", filtered)])
        | .error _ =>
            pure ()
      let cts : Array CertifiedThm ← ExceptT.lift allCertifiedThms
      let filtered :=
        cts.filter (fun ct =>
          (match cat? with | none => true | some c => ct.block.category == c) &&
          (match kind? with | none => true | some k => ct.block.kind == k))
      let js : Array Json := filtered.map (fun ct : CertifiedThm => Lean.toJson (summarizeCertified ct))
      return mkOk (Json.mkObj [("theorems", Json.arr js)])
  | "get_theorem"
  | "get_certified_theorem" => do
      let n ← liftExcept <| expectString req "name"
      let nameParsed := parseThmName n
      match findThmByName nameParsed with
      | none => return mkOk (Json.mkObj [("theorem", Json.null)])
      | some b =>
          let cert ← ExceptT.lift <| getThmCert b
          let summary := summarizeCertified { block := b, cert := cert }
          return mkOk (Json.mkObj [("theorem", Lean.toJson summary)])
  | "list_processes" => do
      let js ← ExceptT.lift apiListProcesses
      return mkOk (Json.mkObj [("processes", js)])
  | "run_process" => do
      let out ← ExceptT.lift (apiRunProcess req)
      return mkOk out
  | other => throwErr s!"unknown command '{other}'"

def evalRequest (req : Json) : IO Json := do
  match ← (handleRequest req).run with
  | Except.ok resp    => pure resp
  | Except.error msg  => pure (mkErr msg)

/-- Load theorems manifest JSON from disk without triggering discovery. -/
def evalRequestUsingManifest (manifestPath : System.FilePath) (req : Json) : IO Json := do
  let manifest ← loadTheoremManifest manifestPath
  let cmd ← match req.getObjValAs? String "command" with
    | .ok c => pure c
    | .error e => throw <| IO.userError e
  match cmd with
  | "list_theorems" | "list_certified_theorems" =>
      let cat? := optString req "category"
      let kind? := optString req "kind"
      let theorems := filterManifestTheorems manifest cat? kind?
      pure <| mkOk (Json.mkObj [("theorems", theorems)])
  | "get_theorem" | "get_certified_theorem" =>
      let nm ← match req.getObjValAs? String "name" with
        | .ok v => pure v
        | .error e => throw <| IO.userError e
      let entry := manifestLookup manifest nm
      pure <| mkOk (Json.mkObj [("theorem", entry)])
  | other =>
      throw <| IO.userError s!"unsupported command in manifest eval: {other}"

def sampleResponse : IO Json :=
  evalRequest sampleRequest

/-! ## Exported entry point -/

@[export apmt_pcc_eval_json_lean]
def apmtPccEvalJson (req : @& ByteArray) : IO ByteArray := do
  let str ← match String.fromUTF8? req with
    | some s => pure s
    | none   => throw <| IO.userError "request must be valid UTF-8"
  let json ← match Json.parse str with
    | Except.ok j      => pure j
    | Except.error err => throw <| IO.userError s!"JSON parse error: {err}"
  let out ← evalRequest json
  pure out.compress.toUTF8

@[export apmt_pcc_eval_string]
def apmtPccEvalString (req : @& String) : IO String := do
  let json ← match Json.parse req with
    | Except.ok j      => pure j
    | Except.error err => throw <| IO.userError s!"JSON parse error: {err}"
  let out ← evalRequest json
  pure out.compress

/-- String-input JSON evaluator (for C shim convenience). -/
@[export apmt_pcc_eval_json_string]
def apmtPccEvalJsonString (req : @& String) : IO String := do
  let json ← match Json.parse req with
    | Except.ok j      => pure j
    | Except.error err => throw <| IO.userError s!"JSON parse error: {err}"
  let out ← evalRequest json
  pure out.compress

/-- Manifest-backed lightweight eval for embedding (limited command set). -/
@[export apmt_pcc_eval_manifest_json_lean]
def apmtPccEvalManifestJson (manifestPath : @& ByteArray) (req : @& ByteArray) : IO String := do
  try
    -- Prefer caller path if valid UTF-8; otherwise fall back to default manifest path.
    let mp := match String.fromUTF8? manifestPath with
      | some s => System.FilePath.mk s
      | none   => System.FilePath.mk ".." / HeytingLean.Theorems.manifestPath
    let str ← match String.fromUTF8? req with
      | some s => pure s
      | none   => throw <| IO.userError "request must be valid UTF-8"
    let json ← match Json.parse str with
      | Except.ok j      => pure j
      | Except.error err => throw <| IO.userError s!"JSON parse error: {err}"
    let out ← evalRequestUsingManifest mp json
    pure out.pretty
  catch e =>
    pure <| mkErr (toString e) |>.pretty

/-- Manifest eval with String inputs (for C shim convenience). -/
@[export apmt_pcc_eval_manifest_string]
def apmtPccEvalManifestString (manifestPath : @& String) (req : @& String) : IO String := do
  try
    let mp : System.FilePath := System.FilePath.mk manifestPath
    let json ← match Json.parse req with
      | Except.ok j      => pure j
      | Except.error err => throw <| IO.userError s!"JSON parse error: {err}"
    let out ← evalRequestUsingManifest mp json
    pure out.pretty
  catch e =>
    pure <| mkErr (toString e) |>.pretty

/-- Simple ping to verify Lean init from C. -/
@[export apmt_pcc_ping_lean]
def apmtPccPing : IO String :=
  pure "ok"

end PCC
end HeytingLean
