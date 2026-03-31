import Lean
import Lean.Data.Json
import Mathlib.Data.Finset.Basic
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.Export
import HeytingLean.CCI.Cert
import HeytingLean.CCI.Json
import HeytingLean.CCI.CryptoSpecs
import HeytingLean.Blockchain.Contracts.PEGv0
import HeytingLean.CLI.Args

namespace HeytingLean
namespace Blockchain
namespace Contracts
namespace CLI
namespace PEGDemo

open IO
open Lean
open HeytingLean.Crypto
open HeytingLean.Crypto.BoolLens
open HeytingLean.Crypto.ZK
open HeytingLean.CCI
open HeytingLean.CCI.CryptoSpecs
open HeytingLean.Blockchain.Contracts
open Finset

/-- Try to read a file, returning an explanatory error string on failure. -/
def readFileE (path : System.FilePath) : IO (Except String String) := do
  try
    let s ← FS.readFile path
    pure (.ok s)
  catch e =>
    pure (.error s!"read error at {path}: {e}")

structure StepJ where
  toAddr      : Nat
  vendor      : Nat
  spentNow    : Nat
  unitPrice   : Nat
  agreedPrice : Nat
  budget      : Nat
  fnId        : Nat
  whitelist   : Array Nat
  now         : Nat
  startTs     : Nat
  endTs       : Nat
  deriving Inhabited

namespace StepJ

open Lean (Json)

private def orErr {α} : Option α → String → Except String α
  | some a, _ => .ok a
  | none, msg => .error msg

def fromJsonE (j : Json) : Except String StepJ := do
  let o ← j.getObj?
  let toAddr      ← (orErr (o.get? "toAddr") "missing toAddr")      >>= (fun t => t.getNat?)
  let vendor      ← (orErr (o.get? "vendor") "missing vendor")      >>= (fun t => t.getNat?)
  let spentNow    ← (orErr (o.get? "spentNow") "missing spentNow")   >>= (fun t => t.getNat?)
  let unitPrice   ← (orErr (o.get? "unitPrice") "missing unitPrice") >>= (fun t => t.getNat?)
  let agreedPrice ← (orErr (o.get? "agreedPrice") "missing agreedPrice") >>= (fun t => t.getNat?)
  let budget      ← (orErr (o.get? "budget") "missing budget")      >>= (fun t => t.getNat?)
  let fnId        ← (orErr (o.get? "fnId") "missing fnId")          >>= (fun t => t.getNat?)
  let whitelistArr ← (orErr (o.get? "whitelist") "missing whitelist") >>= (fun t => t.getArr?)
  let now         ← (orErr (o.get? "now") "missing now")             >>= (fun t => t.getNat?)
  let startTs     ← (orErr (o.get? "startTs") "missing startTs")     >>= (fun t => t.getNat?)
  let endTs       ← (orErr (o.get? "endTs") "missing endTs")         >>= (fun t => t.getNat?)
  -- collect nat entries from the array, dropping invalid items
  let whitelist := whitelistArr.filterMap (fun x =>
    match x.getNat? with
    | .ok n => some n
    | .error _ => none)
  pure {
    toAddr, vendor, spentNow, unitPrice, agreedPrice, budget,
    fnId := fnId,
    whitelist := whitelist,
    now, startTs, endTs
  }

end StepJ

def writeFile (path : System.FilePath) (content : String) : IO Unit :=
  FS.writeFile path content

/-- Encode a `Certificate` as JSON, mirroring the format used by
    `CCICryptoExport`. -/
def encodeCertStr (c : Certificate) : String :=
  let q (s : String) : String :=
    "\"" ++ HeytingLean.CCI.jsonEscape s ++ "\""
  let inputs :=
    let arr := c.inputs.map (fun (k,v) =>
      "{" ++ "\"k\":" ++ q k ++ ",\"v\":" ++ q v ++ "}")
    "[" ++ String.intercalate "," arr ++ "]"
  let omega  := HeytingLean.CCI.encodeExprStr c.omega
  let lenses :=
    let items := c.lensImgs.map (fun l => HeytingLean.CCI.encodeLensStr l)
    "[" ++ String.intercalate "," items ++ "]"
  let rws    :=
    let items := c.rewrites.map (fun (n : HeytingLean.CCI.RuleId) => toString n)
    "[" ++ String.intercalate "," items ++ "]"
  let digs   :=
    let hexOf (d : HeytingLean.CCI.Digest) : String :=
      let parts := d.toList.map (fun b =>
        let s := (Nat.toDigits 16 b.toNat).asString
        if s.length = 1 then "0" ++ s else s)
      String.intercalate "" parts
    let mk : (HeytingLean.CCI.Path × HeytingLean.CCI.Digest) → String :=
      fun (p,d) =>
        "{" ++ "\"path\":" ++ q p ++ ",\"digest\":" ++ q (hexOf d) ++ "}"
    let items := c.digests.map mk
    "[" ++ String.intercalate "," items ++ "]"
  "{" ++
    "\"inputs\":" ++ inputs ++ "," ++
    "\"omega\":" ++ omega ++ "," ++
    "\"lenses\":" ++ lenses ++ "," ++
    "\"rewrites\":" ++ rws ++ "," ++
    "\"digests\":" ++ digs ++
  "}"

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | [stepPath, outDir] =>
      let raw ← match (← readFileE stepPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let j ← match Json.parse raw with | .ok j => pure j | .error err => eprintln err; return 1
      let sJ ← match StepJ.fromJsonE j with | .ok s => pure s | .error err => eprintln err; return 1
      -- Convert to PEGv0.Step
      let s : Contracts.Step := {
        toAddr := sJ.toAddr
        vendor := sJ.vendor
        spentNow := sJ.spentNow
        unitPrice := sJ.unitPrice
        agreedPrice := sJ.agreedPrice
        budget := sJ.budget
        fnId := UInt32.ofNat sJ.fnId
        whitelist := sJ.whitelist.toList.foldl (fun acc n => insert (UInt32.ofNat n) acc) ({} : Finset UInt32)
        now := sJ.now
        startTs := sJ.startTs
        endTs := sJ.endTs
      }
      -- Compute decision and compile/export artefacts
      let φ : Form 5 := Contracts.PEGv0.permitForm
      let ρ : Env 5 := Contracts.PEGv0.envOf s
      let decision := BoolLens.eval φ ρ
      let compiled := ZK.R1CSBool.compile φ ρ
      let r1csJson := ZK.Export.systemToJson compiled.system |>.compress
      let maxVar := compiled.system.constraints.foldl (init := 0) (fun m c =>
        let step := fun acc (ts : List (ZK.Var × ℚ)) => ts.foldl (fun a p => Nat.max a p.fst) acc
        let m1 := step 0 c.A.terms
        let m2 := step m1 c.B.terms
        let m3 := step m2 c.C.terms
        Nat.max m m3)
      let numVars := maxVar + 1
      let witnessJson := ZK.Export.assignmentToJson compiled.assignment numVars |>.compress
      let metaJ := Json.mkObj
        [ ("outputVar", Json.num compiled.output)
        , ("eval", Json.str (toString decision))
        , ("backend", Json.str "r1cs")
        ] |>.compress
      let decJ := Json.mkObj
        [ ("permit", Json.bool decision)
        , ("vars", Json.arr #[(Json.bool (ρ ⟨0, by decide⟩)), (Json.bool (ρ ⟨1, by decide⟩)), (Json.bool (ρ ⟨2, by decide⟩)), (Json.bool (ρ ⟨3, by decide⟩)), (Json.bool (ρ ⟨4, by decide⟩))])
        ] |>.compress
      -- Minimal CCI certificate keyed by a PEGv0-specific slug, with
      -- public inputs reflecting the step fields. This mirrors the
      -- structure produced by `CCICryptoExport`.
      let inputs : PublicInputs :=
        [ ("toAddr",      toString s.toAddr)
        , ("vendor",      toString s.vendor)
        , ("spentNow",    toString s.spentNow)
        , ("unitPrice",   toString s.unitPrice)
        , ("agreedPrice", toString s.agreedPrice)
        , ("budget",      toString s.budget)
        , ("fnId",        toString s.fnId)
        , ("now",         toString s.now)
        , ("startTs",     toString s.startTs)
        , ("endTs",       toString s.endTs)
        , ("permit",      toString decision)
        ]
      let cert : Certificate :=
        mkCertificateFromSlug "contracts.pegv0_guard" inputs
      let certJson := encodeCertStr cert
      let outR1cs := System.FilePath.mk outDir / "r1cs.json"
      let outWitness := System.FilePath.mk outDir / "witness.json"
      let outMeta := System.FilePath.mk outDir / "meta.json"
      let outDecision := System.FilePath.mk outDir / "decision.json"
      let outCert := System.FilePath.mk outDir / "cert.json"
      FS.createDirAll (System.FilePath.mk outDir)
      writeFile outR1cs r1csJson
      writeFile outWitness witnessJson
      writeFile outMeta metaJ
      writeFile outDecision decJ
      writeFile outCert certJson
      println s!"Permit: {decision}"
      println s!"wrote {outR1cs} {outWitness} {outMeta} {outDecision} {outCert}"
      pure 0
  | _ =>
      eprintln "Usage: lake exe peg_demo <step.json> <outdir>"
      pure 1

end PEGDemo
end CLI
end Contracts
end Blockchain
end HeytingLean

-- Provide a top-level main alias for the executable linker
open HeytingLean.Blockchain.Contracts.CLI.PEGDemo in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Blockchain.Contracts.CLI.PEGDemo.main args
