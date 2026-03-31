import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Geo.GQRE.Core
import HeytingLean.Geo.GQRE.PMFlow
import HeytingLean.Occam.GQRE

/-!
# GQRE / PM receipt verifier executable

This executable ingests a `GQREReport.v1` JSON file emitted by
`tools/gqre/pm_flow.py`, recomputes the GQRE quantities in Lean,
and checks them against the reported values and simple thresholds.
-/

namespace HeytingLean.Exec.GQRE.VerifyPM

open Lean
open Lean.Json
open HeytingLean.Geo.GQRE

/-- Minimal view of a GQRE report sufficient for verification. -/
structure Report where
  alpha          : Float
  dt             : Float
  iters          : Nat
  qEdge          : Float
  φIn            : Field2
  φOut           : Field2
  width          : Nat
  height         : Nat
  hashIn         : String
  hashOut        : String
  S_in           : Float
  S_out          : Float
  Lgqre_mean_in  : Float
  Lgqre_mean_out : Float
  edge_preserve  : Float
  deriving Repr

/-- Verification configuration. For now we only support tolerances and
simple lower/upper bounds; in a real pipeline this can be wired to
contracts. -/
structure VerifyConfig where
  deltaMin  : Float := 0.0    -- minimum acceptable S_out - S_in
  edgeMin   : Float := 0.0    -- minimum acceptable edge_preserve
  lagMaxOut : Option Float := none -- optional upper bound for Lgqre_mean_out
  tolRel    : Float := 1e-3   -- relative tolerance when comparing floats
  tolAbs    : Float := 1e-6   -- absolute tolerance
  deriving Repr

/-- Parse a `GQREReport.v1` JSON object into a `Report`. -/
def parseReport (j : Json) : Except String Report := do
  let getObj (j : Json) : Except String Json := do
    match j.getObj? with
    | .ok _ => pure j
    | .error _ => .error "expected object"
  let metaJ ← match j.getObjVal? "meta" with
    | .ok m => getObj m
    | .error _ => .error "missing or invalid 'meta' field"

  let grabFloat (obj : Json) (k : String) : Except String Float := do
    match obj.getObjVal? k with
    | .ok v =>
        match v.getNum? with
        | .ok n =>
            -- Interpret the JSON number via string; we expect the Python
            -- emitter to use standard decimal notation.
            let s := n.toString
            match String.toNat? s with
            | some nNat => .ok (Float.ofNat nNat)
            | none =>
                -- Fallback: very small lexer for simple decimal floats.
                match s.splitOn "." with
                | [intPart, fracPart] =>
                    match String.toNat? intPart, String.toNat? fracPart with
                    | some i, some f =>
                        let scale := 10.0 ^ (Float.ofNat fracPart.length)
                        .ok (Float.ofNat i + Float.ofNat f / scale)
                    | _, _ => .error s!"field '{k}' not a simple decimal Float"
                | _ => .error s!"field '{k}' not a Nat or decimal Float"
        | .error _ => .error s!"field '{k}' not a number"
    | .error _ => .error s!"missing field '{k}'"

  let grabNat (obj : Json) (k : String) : Except String Nat := do
    match obj.getObjVal? k with
    | .ok v =>
        match v.getNat? with
        | .ok n => .ok n
        | .error _ => .error s!"field '{k}' not a Nat"
    | .error _ => .error s!"missing field '{k}'"

  let grabStr (obj : Json) (k : String) : Except String String := do
    match obj.getObjVal? k with
    | .ok v =>
        match v.getStr? with
        | .ok s => .ok s
        | .error _ => .error s!"field '{k}' not a String"
    | .error _ => .error s!"missing field '{k}'"

  let alpha ← grabFloat metaJ "alpha"
  let dt ← grabFloat metaJ "dt"
  let itersNat ← grabNat metaJ "iters"
  let iters : Nat := itersNat
  let qEdge ← grabFloat metaJ "q_edge"
  let width ← grabNat metaJ "width"
  let height ← grabNat metaJ "height"

  let hashIn ← grabStr j "hash_in"
  let hashOut ← grabStr j "hash_out"

  -- Parse nested float arrays for fields.
  let parseFloat (v : Json) : Except String Float := do
    match v.getNum? with
    | .ok n =>
        let s := n.toString
        match String.toNat? s with
        | some nNat => .ok (Float.ofNat nNat)
        | none =>
            match s.splitOn "." with
            | [intPart, fracPart] =>
                match String.toNat? intPart, String.toNat? fracPart with
                | some i, some f =>
                    let scale := (10.0 : Float) ^ (Float.ofNat fracPart.length)
                    .ok (Float.ofNat i + Float.ofNat f / scale)
                | _, _ => .error "bad decimal float"
            | _ => .error "unsupported float encoding"
    | .error _ => .error "expected JSON number"

  let parseField2 (key : String) : Except String Field2 := do
    match j.getObjVal? key with
    | .ok (Json.arr rows) =>
        let rec parseRows (rs : List Json) (acc : Field2) :
            Except String Field2 := do
          match rs with
          | [] => .ok acc
          | r :: rt =>
              match r.getArr? with
              | .ok cols =>
                  let rec parseCols (cs : List Json) (rowAcc : Array Float) :
                      Except String (Array Float) := do
                    match cs with
                    | [] => .ok rowAcc
                    | c :: ct =>
                        let v ← parseFloat c
                        parseCols ct (rowAcc.push v)
                  let row ← parseCols cols.toList #[]
                  parseRows rt (acc.push row)
              | .error _ => .error s!"field '{key}' row not an array"
        parseRows rows.toList #[]
    | _ => .error s!"missing or invalid field '{key}'"

  let φIn ← parseField2 "field_in"
  let φOut ← parseField2 "field_out"

  let numField (k : String) : Except String Float := grabFloat j k

  let S_in ← numField "S_in"
  let S_out ← numField "S_out"
  let L_in ← numField "Lgqre_mean_in"
  let L_out ← numField "Lgqre_mean_out"
  let edge_preserve ← numField "edge_preserve"

  pure {
    alpha := alpha
    dt := dt
    iters := iters
    qEdge := qEdge
    φIn := φIn
    φOut := φOut
    width := width
    height := height
    hashIn := hashIn
    hashOut := hashOut
    S_in := S_in
    S_out := S_out
    Lgqre_mean_in := L_in
    Lgqre_mean_out := L_out
    edge_preserve := edge_preserve
  }

/-- Simple absolute/relative float comparison helper. -/
def approxEq (cfg : VerifyConfig) (x y : Float) : Bool :=
  let diff := Float.abs (x - y)
  if diff ≤ cfg.tolAbs then
    true
  else
    let ax := Float.abs x
    let ay := Float.abs y
    let denom := if ax ≥ ay then ax else ay
    if denom == 0.0 then
      diff ≤ cfg.tolAbs
    else
      diff / denom ≤ cfg.tolRel

/-- Verification result with a reason on failure. -/
inductive VerificationResult
  | ok
  | mismatch (msg : String)
  deriving Repr

/-- Verify a report against simple guard thresholds. For this first
cut we recompute the GQRE quantities in Lean from the embedded fields
and check both thresholds and agreement with the reported scalars. -/
def verifyReport (cfg : VerifyConfig) (rep : Report) : VerificationResult :=
  let p : Params := { alpha := rep.alpha }
  let gIn := grad rep.φIn
  let gOut := grad rep.φOut
  let S_in_re := action p gIn.gx gIn.gy
  let S_out_re := action p gOut.gx gOut.gy
  let L_in_re := lagMean p gIn.gx gIn.gy
  let L_out_re := lagMean p gOut.gx gOut.gy
  let edge_re := HeytingLean.Occam.GQRE.edgePreserve rep.φIn rep.φOut rep.qEdge
  let gain := S_out_re - S_in_re
  if ¬ approxEq cfg S_in_re rep.S_in then
    VerificationResult.mismatch s!"S_in mismatch: recomputed={S_in_re}, reported={rep.S_in}"
  else if ¬ approxEq cfg S_out_re rep.S_out then
    VerificationResult.mismatch s!"S_out mismatch: recomputed={S_out_re}, reported={rep.S_out}"
  else if ¬ approxEq cfg L_in_re rep.Lgqre_mean_in then
    VerificationResult.mismatch s!"Lgqre_mean_in mismatch: recomputed={L_in_re}, reported={rep.Lgqre_mean_in}"
  else if ¬ approxEq cfg L_out_re rep.Lgqre_mean_out then
    VerificationResult.mismatch s!"Lgqre_mean_out mismatch: recomputed={L_out_re}, reported={rep.Lgqre_mean_out}"
  else if ¬ approxEq cfg edge_re rep.edge_preserve then
    VerificationResult.mismatch s!"edge_preserve mismatch: recomputed={edge_re}, reported={rep.edge_preserve}"
  else if ¬ (gain ≥ cfg.deltaMin) then
    VerificationResult.mismatch s!"GQREGain too small: {gain} < {cfg.deltaMin}"
  else if ¬ (edge_re ≥ cfg.edgeMin) then
    VerificationResult.mismatch s!"edge_preserve too small: {edge_re} < {cfg.edgeMin}"
  else
    match cfg.lagMaxOut with
    | some ub =>
        if ¬ (L_out_re ≤ ub) then
          VerificationResult.mismatch s!"Lgqre_mean_out too large: {L_out_re} > {ub}"
        else
          VerificationResult.ok
    | none =>
        VerificationResult.ok

/-- Render a small JSON commitment summarising the verification. -/
def renderCommitment (rep : Report) (res : VerificationResult) : Json :=
  let status : String :=
    match res with
    | .ok => "ok"
    | .mismatch _ => "fail"
  let base : List (String × Json) :=
    [ ("status", Json.str status)
    , ("S_in", Json.str (toString rep.S_in))
    , ("S_out", Json.str (toString rep.S_out))
    , ("Lgqre_mean_in", Json.str (toString rep.Lgqre_mean_in))
    , ("Lgqre_mean_out", Json.str (toString rep.Lgqre_mean_out))
    , ("edge_preserve", Json.str (toString rep.edge_preserve))
    , ("alpha", Json.str (toString rep.alpha))
    , ("dt", Json.str (toString rep.dt))
    , ("iters", Json.num rep.iters)
    ]
  let fields :=
    match res with
    | .ok => base
    | .mismatch msg => ("reason", Json.str msg) :: base
  Json.mkObj fields

/-- CLI entry point: `lake exe gqre_verify_pm path/to/gqre.json [--delta δ] [--tau τ] [--lag-max ub]`. -/
def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | reportPath :: rest =>
      let cfg0 : VerifyConfig := {}
      let rec parseFlags (xs : List String) (c : VerifyConfig) : IO VerifyConfig :=
        match xs with
        | [] => pure c
        | "--delta" :: v :: tail =>
            match v.toNat? with
            | some n => parseFlags tail { c with deltaMin := Float.ofNat n }
            | none => parseFlags tail c
        | "--tau" :: v :: tail =>
            match v.toNat? with
            | some n => parseFlags tail { c with edgeMin := Float.ofNat n }
            | none => parseFlags tail c
        | "--lag-max" :: v :: tail =>
            match v.toNat? with
            | some n => parseFlags tail { c with lagMaxOut := some (Float.ofNat n) }
            | none => parseFlags tail c
        | _ :: tail =>
            parseFlags tail c
      let cfg ← parseFlags rest cfg0
      let raw? : Option String ← do
        try
          let s ← IO.FS.readFile (System.FilePath.mk reportPath)
          pure (some s)
        catch e =>
          IO.eprintln s!"read error: {e}"
          pure none
      let raw ← match raw? with
        | some s => pure s
        | none => return 1
      let j ←
        match Json.parse raw with
        | .ok v => pure v
        | .error e =>
            IO.eprintln s!"JSON parse error: {e}"
            pure Json.null
      match parseReport j with
      | .error msg =>
          IO.eprintln s!"report parse error: {msg}"
          pure 1
      | .ok rep =>
          let res := verifyReport cfg rep
          let commitment := renderCommitment rep res
          IO.println commitment.compress
          match res with
          | .ok => pure 0
          | .mismatch _ => pure 2
  | _ =>
      IO.eprintln "usage: lake exe gqre_verify_pm <report.json> [--delta δ] [--tau τ] [--lag-max ub]"
      pure 1

end HeytingLean.Exec.GQRE.VerifyPM

open HeytingLean.Exec.GQRE.VerifyPM in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Exec.GQRE.VerifyPM.main args
