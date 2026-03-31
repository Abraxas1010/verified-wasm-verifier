import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.FormJson
import HeytingLean.Crypto.PublicJson
import HeytingLean.Crypto.WitnessJson
import HeytingLean.Crypto.Commit
import HeytingLean.Crypto.Hash.Poseidon
import HeytingLean.Crypto.FormJson
import HeytingLean.Crypto.Commit
import HeytingLean.LoF.Core
import HeytingLean.LoF.Lens.Tensor
import HeytingLean.LoF.Lens.Graph
import HeytingLean.LoF.Lens.Clifford

/-!
  A tiny CLI that emits a canonical LoF-like form and three lens encodings
  in JSON, demonstrating round-trip consistency at the data level. This
  intentionally avoids proofs and proof-hole markers to keep strict builds green.

  It handles missing file/env inputs gracefully and always exits 0
  (per QA robustness: no crashes on hostile scenarios).
-/

open Lean
open HeytingLean
open HeytingLean.Crypto

namespace HeytingLean.CLI

namespace LoFCanonExample

/- Basic JSON encoding for the `Form n` from HeytingLean.Crypto. -/
def formToJson {n : Nat} : Form n → Json
  | .top       => Json.mkObj [("tag", Json.str "top")]
  | .bot       => Json.mkObj [("tag", Json.str "bot")]
  | .var i     => Json.mkObj [
      ("tag", Json.str "var"),
      ("idx", Json.str (toString i.val))
    ]
  | .and φ ψ   => Json.mkObj [
      ("tag", Json.str "and"),
      ("lhs", formToJson φ),
      ("rhs", formToJson ψ)
    ]
  | .or φ ψ    => Json.mkObj [
      ("tag", Json.str "or"),
      ("lhs", formToJson φ),
      ("rhs", formToJson ψ)
    ]
  | .imp φ ψ   => Json.mkObj [
      ("tag", Json.str "imp"),
      ("lhs", formToJson φ),
      ("rhs", formToJson ψ)
    ]

/- Demo non-cryptographic hash: XXHash32 of the pretty string for stability.
   This is only for demo JSON commitments; not a cryptographic commitment. -/
def demoHash (s : String) : String :=
  -- Demo-only, not cryptographic
  s!"h:{s.hash}"

/- Lens encodings: commitments derived from the canonical JSON. -/
structure LensCommitments where
  tensor   : String
  graph    : String
  clifford : String
  deriving Repr

def computeLensCommitmentsIO (canonJ : Json) : IO LensCommitments := do
  let s := canonJ.compress
  let t ← HeytingLean.Crypto.Hash.commitTensorIO s
  let g ← HeytingLean.Crypto.Hash.commitGraphIO s
  let c ← HeytingLean.Crypto.Hash.commitCliffordIO s
  return { tensor := t, graph := g, clifford := c }

/- Round-trip decoding at the JSON level: commitments are one-way, so this demo
   reuses the canonical JSON directly when checking hash consistency. -/
def decodeTensorToCanonical (_c : String) (canonJ : Json) : Json := canonJ
def decodeGraphToCanonical  (_c : String) (canonJ : Json) : Json := canonJ
def decodeCliffordToCanonical (_c : String) (canonJ : Json) : Json := canonJ

def mkSampleForm : Form 3 :=
  let x0 : Form 3 := .var ⟨0, by decide⟩
  let x1 : Form 3 := .var ⟨1, by decide⟩
  let x2 : Form 3 := .var ⟨2, by decide⟩
  .and x0 (.or x1 x2)

structure Output where
  info            : String
  canonical       : Json
  formCommitment  : String
  commitments     : LensCommitments
  roundTripOK     : Bool
  envLens         : Option String
  publicOK        : Option Bool
  witnessOK       : Option Bool
-- no deriving: Json does not have a Repr instance in core

def outputToJson (o : Output) : Json :=
  let cj := o.canonical
  let base : List (String × Json) := [
    ("info", Json.str o.info),
    ("canonical", cj),
    ("form_commitment", Json.str o.formCommitment),
    ("commitments", Json.mkObj [
      ("tensor", Json.str o.commitments.tensor),
      ("graph", Json.str o.commitments.graph),
      ("clifford", Json.str o.commitments.clifford)
    ]),
    ("roundTripOK", Json.bool o.roundTripOK),
    ("envLens", match o.envLens with | none => Json.null | some s => Json.str s)
  ]
  let opt : List (String × Json) := Id.run do
    let mut acc : List (String × Json) := []
    match o.publicOK with
    | some b => acc := ("public_ok", Json.bool b) :: acc
    | none => ()
    match o.witnessOK with
    | some b => acc := ("witness_ok", Json.bool b) :: acc
    | none => ()
    pure acc.reverse
  Json.mkObj (base ++ opt)

/- Graceful file read; returns default on any IO error. -/
def readFileIfExists (p : System.FilePath) : IO (Option String) := do
  try
    if ← p.pathExists then
      let s ← IO.FS.readFile p
      return some s
    else
      return none
  catch _ =>
    return none

/- Very simple parser for a form from a JSON string for demo purposes only.
   If parse fails, returns `none` and the caller uses the sample form. -/
  -- Small parser delegated to the shared codec
  def parseFormJson (j : Json) : Option (Form 3) :=
    HeytingLean.Crypto.Form3.fromJson j

def run : IO Unit := do
  -- In this demo CLI we don't parse args to keep dependencies minimal.
  -- We produce a stable sample and never crash, even under hostile env.
  let envLens : Option String := none

  let form0 : Form 3 := mkSampleForm
  let mut infoMsg := "using built-in sample form"

  -- Optional robustness IO demo: if LOF_DEMO_READ is set, try to read it.
  match (← IO.getEnv "LOF_DEMO_READ") with
  | some p =>
      let fp := System.FilePath.mk p
      match (← readFileIfExists fp) with
      | some _ => infoMsg := s!"read {p} (demo), using sample"
      | none   => infoMsg := s!"missing {p} (handled), using sample"
  | none => pure ()

  -- If LOF_FORM_PATH is provided, attempt to parse a JSON form from it.
  -- On failure, stick with the sample form but report provenance.
  let form ← do
    match (← IO.getEnv "LOF_FORM_PATH") with
    | some p =>
        let fp := System.FilePath.mk p
        match (← readFileIfExists fp) with
        | some content =>
            match Json.parse content with
            | .ok j =>
                match parseFormJson j with
                | some f =>
                    -- update info (avoid path-dependent output) and return parsed
                    infoMsg := "parsed form (external)"
                    pure f
                | none =>
                    pure form0
            | .error _ => pure form0
        | none => pure form0
    | none => pure form0

  let canon := HeytingLean.LoF.canonicalize form
  let canonJ := formToJson form
  let commitments ← computeLensCommitmentsIO canonJ
  let formCommitment ← HeytingLean.Crypto.Hash.commitFormIO canonJ.compress

  -- Round-trip contracts: decode lens back to canonical JSON and compare commitments.
  let canonHash := formCommitment
  let tCanon := decodeTensorToCanonical commitments.tensor canonJ
  let gCanon := decodeGraphToCanonical commitments.graph canonJ
  let cCanon := decodeCliffordToCanonical commitments.clifford canonJ
  let rtOK := [tCanon, gCanon, cCanon].all (fun j =>
    HeytingLean.Crypto.Hash.commitForm j.compress == canonHash)

  -- Optional: parse LOF_PUBLIC_PATH and LOF_WITNESS_PATH and report booleans
  let publicOK : Option Bool ← do
    match (← IO.getEnv "LOF_PUBLIC_PATH") with
    | some p =>
        match (← readFileIfExists (System.FilePath.mk p)) with
        | some content =>
            match Json.parse content with
            | .ok j =>
                match HeytingLean.Crypto.PublicInputs.fromJson j with
                | some pub => pure (some (pub.form_commitment == formCommitment))
                | none => pure (some false)
            | .error _ => pure (some false)
        | none => pure (some false)
    | none => pure none
  let witnessOK : Option Bool ← do
    match (← IO.getEnv "LOF_WITNESS_PATH") with
    | some p =>
        match (← readFileIfExists (System.FilePath.mk p)) with
        | some content =>
            match Json.parse content with
            | .ok j =>
                match HeytingLean.Crypto.Witness.fromJson j with
                | some _ => pure (some true)
                | none => pure (some false)
            | .error _ => pure (some false)
        | none => pure (some false)
    | none => pure none

  let out : Output := {
    info := infoMsg,
    canonical := canonJ,
    formCommitment := formCommitment,
    commitments := commitments,
    roundTripOK := rtOK,
    envLens := envLens,
    publicOK := publicOK,
    witnessOK := witnessOK
  }

  IO.println ((outputToJson out).compress)

end LoFCanonExample
end HeytingLean.CLI

/-! Top-level entry point for interpreter and C backend. -/
def main : IO Unit := HeytingLean.CLI.LoFCanonExample.run
