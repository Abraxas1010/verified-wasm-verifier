import Lean
import Lean.Data.Json
import HeytingLean.Bridges.Emergence
import HeytingLean.CLI.Args

/-
Emergence Selector report checker executable
============================================

This executable ingests a JSON report emitted by
`tools/emergence/selector.py` and performs basic structural checks:

* the TPM dimension `n` matches the candidate partitions,
* each candidate is a genuine partition of `{0,…,n−1}` (no duplicates,
  no missing states, no empty blocks),
* the chosen index is within bounds.

Numeric CP / ΔCP values are currently trusted as‐is and are not
recomputed in Lean; they live at the Python heuristic layer. The Lean
side focuses on structural validity and compatibility with the
`HeytingLean.Bridges.Emergence` types.
-/

namespace HeytingLean.Exec.Emergence.SelectMain

open Lean
open Lean.Json
open Std
open HeytingLean.Bridges
open HeytingLean.Bridges.Emergence

/-- Minimal view of an emergence selector report sufficient for
structural checking. -/
structure Report where
  n          : Nat
  candidates : List (List (List Nat))
  chosen     : Nat
  deltaCP    : List Float
  S_path     : Float
  S_row      : Float
  regime     : String
  deriving Repr

/-- Parse a selector JSON object into a `Report`. -/
def parseReport (j : Json) : Except String Report := do
  let obj ←
    match j.getObj? with
    | .ok _ => pure j
    | .error _ => .error "expected top‑level JSON object"

  let getNat (k : String) : Except String Nat := do
    match obj.getObjVal? k with
    | .ok v =>
        match v.getNat? with
        | .ok n => pure n
        | .error _ => .error s!"field '{k}' not a Nat"
    | .error _ => .error s!"missing field '{k}'"

  let getStr (k : String) : Except String String := do
    match obj.getObjVal? k with
    | .ok v =>
        match v.getStr? with
        | .ok s => pure s
        | .error _ => .error s!"field '{k}' not a String"
    | .error _ => .error s!"missing field '{k}'"

  -- Minimal decimal float parser compatible with the Python emitter.
  let parseFloatLit (s : String) : Except String Float := do
    match String.toNat? s with
    | some nNat => pure (Float.ofNat nNat)
    | none =>
        match s.splitOn "." with
        | [intPart, fracPart] =>
            match String.toNat? intPart, String.toNat? fracPart with
            | some i, some f =>
                let scale := (10.0 : Float) ^ (Float.ofNat fracPart.length)
                pure (Float.ofNat i + Float.ofNat f / scale)
            | _, _ => .error "bad decimal float"
        | _ => .error "unsupported float encoding"

  let getFloat (k : String) : Except String Float := do
    match obj.getObjVal? k with
    | .ok v =>
        match v.getNum? with
        | .ok n =>
            -- interpret the JSON number via string
            let s := n.toString
            parseFloatLit s
        | .error _ => .error s!"field '{k}' not a number"
    | .error _ => .error s!"missing field '{k}'"

  let getFloatList (k : String) : Except String (List Float) := do
    match obj.getObjVal? k with
    | .ok (Json.arr xs) =>
        let rec goFloats (ys : List Json) (acc : List Float) :
            Except String (List Float) := do
          match ys with
          | [] => pure acc.reverse
          | v :: vs =>
              let f ←
                match v.getNum? with
                | .ok n =>
                    let s := n.toString
                    parseFloatLit s
                | .error _ => .error s!"non‑number in '{k}'"
              goFloats vs (f :: acc)
        goFloats xs.toList []
    | .ok _ => .error s!"field '{k}' not an array"
    | .error _ => .error s!"missing field '{k}'"

  let getCandidates : Except String (List (List (List Nat))) := do
    match obj.getObjVal? "candidates" with
    | .ok (Json.arr xs) =>
        let rec parsePartition (v : Json) : Except String (List (List Nat)) := do
          match v.getArr? with
          | .ok blocks =>
              let rec parseBlocks (bs : List Json) (acc : List (List Nat)) :
                  Except String (List (List Nat)) := do
                match bs with
                | [] => pure acc.reverse
                | b :: bt =>
                    match b.getArr? with
                    | .ok js =>
                        let rec parseStates (ss : List Json) (accS : List Nat) :
                            Except String (List Nat) := do
                          match ss with
                          | [] => pure accS.reverse
                          | s :: st =>
                              match s.getNat? with
                              | .ok n => parseStates st (n :: accS)
                              | .error _ =>
                                  .error "candidate state index not a Nat"
                        let block ← parseStates js.toList []
                        parseBlocks bt (block :: acc)
                    | .error _ =>
                        .error "candidate block not an array"
              parseBlocks blocks.toList []
          | .error _ => .error "candidate not an array of blocks"

        let rec goCand (ys : List Json) (acc : List (List (List Nat))) :
            Except String (List (List (List Nat))) := do
          match ys with
          | [] => pure acc.reverse
          | v :: vs =>
              let π ← parsePartition v
              goCand vs (π :: acc)
        goCand xs.toList []
    | .ok _ => .error "field 'candidates' not an array"
    | .error _ => .error "missing field 'candidates'"

  let _version ← getStr "version" -- currently unused, but parsed for sanity
  let n ← getNat "n"
  let candidates ← getCandidates
  let chosen ← getNat "chosen"
  let deltaCP ← getFloatList "deltaCP"
  let S_path ← getFloat "S_path"
  let S_row ← getFloat "S_row"
  let regime ← getStr "regime"

  pure { n, candidates, chosen, deltaCP, S_path, S_row, regime }

/-- Structural validation result. -/
inductive ValidationResult
  | ok
  | error (msg : String)
  deriving Repr

/-- Check that the candidates form genuine partitions of `{0,…,n−1}` and
that the chosen index is in range. -/
def validate (r : Report) : ValidationResult :=
  if r.candidates.isEmpty then
    ValidationResult.error "no candidates provided"
  else
    let idxMax := r.candidates.length - 1
    if r.chosen > idxMax then
      ValidationResult.error s!"chosen index {r.chosen} out of bounds (max {idxMax})"
    else
      -- check each candidate
      let rec checkCandidates
          (cs : List (List (List Nat))) (k : Nat) :
          ValidationResult :=
        match cs with
        | [] => ValidationResult.ok
        | π :: csTail =>
            -- blocks must be non‑empty and cover/disjoint
            let (seen, ok, _) :=
              π.foldl
                (fun (state : HashSet Nat × Bool × Nat) (b : List Nat) =>
                  let (seen, ok, count) := state
                  if b.isEmpty then
                    (seen, false, count)
                  else
                    b.foldl
                      (fun (state' : HashSet Nat × Bool × Nat) (i : Nat) =>
                        let (seen', ok', count') := state'
                        if i ≥ r.n then
                          (seen', false, count')
                        else if seen'.contains i then
                          (seen', false, count')
                        else
                          (seen'.insert i, ok', count' + 1))
                      (seen, ok, count))
                ((HashSet.emptyWithCapacity : HashSet Nat), true, 0)
            if ¬ ok then
              ValidationResult.error s!"candidate {k} is not a valid partition"
            else if seen.size ≠ r.n then
              ValidationResult.error s!"candidate {k} does not cover all states"
            else
              checkCandidates csTail (k + 1)
      checkCandidates r.candidates 0

/-- Render a compact JSON commitment summarising validation. -/
def renderCommitment (r : Report) (vr : ValidationResult) : Json :=
  let status : String :=
    match vr with
    | .ok => "ok"
    | .error _ => "fail"
  let base : List (String × Json) :=
    [ ("status", Json.str status)
    , ("n", Json.num r.n)
    , ("numCandidates", Json.num r.candidates.length)
    , ("chosen", Json.num r.chosen)
    , ("regime", Json.str r.regime)
    ]
  let fields :=
    match vr with
    | .ok => base
    | .error msg => ("reason", Json.str msg) :: base
  Json.mkObj fields

  /-- CLI entry point: `lake exe emergence_select_check path/to/report.json`. -/
  def main (args : List String) : IO UInt32 := do
    let args := HeytingLean.CLI.stripLakeArgs args
    match args with
    | reportPath :: _ =>
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
            return 1
        | .ok rep =>
            let vr := validate rep
            let commitment := renderCommitment rep vr
            IO.println commitment.compress
            match vr with
            | .ok => return 0
            | .error _ => return 2
    | _ =>
        IO.eprintln "usage: lake exe emergence_select_check <report.json>"
        return 1

end HeytingLean.Exec.Emergence.SelectMain

open HeytingLean.Exec.Emergence.SelectMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Exec.Emergence.SelectMain.main args
