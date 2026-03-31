import Lean
import Lean.Data.Json
import Std

import HeytingLean.Util.JCS
import HeytingLean.Chem.Materials.SLICES.Computable
import HeytingLean.Chem.PeriodicTable.Lookup

/-!
# `slices_bench`

Targeted benchmark harness for the SLICES Phase 1-3 core:
- parse a quotient-graph JSON line (or a raw SLICES string),
- compute `encode` and `canonEncode`,
- sanity check `decode?(encode g)` and report cross-check fields,
- emit one JSON object per input line (JSONL).

This executable is intentionally small and "pipeline-friendly": other scripts can generate datasets,
feed them over stdin, and post-process the JSONL output into aggregate reports and CAB-attested bundles.
-/

namespace HeytingLean.CLI

open Lean
open HeytingLean.Chem.Materials.SLICES
open HeytingLean.Chem.PeriodicTable

private def outputJson (j : Lean.Json) : IO Unit :=
  IO.println (HeytingLean.Util.JCS.canonicalString j)

private def jsonArrE (j : Lean.Json) (ctx : String) : Except String (Array Lean.Json) :=
  match j with
  | .arr xs => .ok xs
  | _ => .error s!"{ctx}: expected JSON array"

private def jsonStrE (j : Lean.Json) (ctx : String) : Except String String :=
  match j with
  | .str s => .ok s
  | _ => .error s!"{ctx}: expected JSON string"

private def jsonNatE (j : Lean.Json) (ctx : String) : Except String Nat := do
  j.getNat? |>.mapError (fun e => s!"{ctx}: {e}")

private def jsonIntE (j : Lean.Json) (ctx : String) : Except String Int := do
  j.getInt? |>.mapError (fun e => s!"{ctx}: {e}")

private def getObjValE (j : Lean.Json) (k : String) (ctx : String) : Except String Lean.Json := do
  j.getObjVal? k |>.mapError (fun e => s!"{ctx}: {e}")

private def getObjValOptStr (j : Lean.Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

private def finOfNatE (n : Nat) (k : Nat) (ctx : String) : Except String (Fin n) :=
  if h : k < n then
    .ok ⟨k, h⟩
  else
    .error s!"{ctx}: index {k} out of range (n={n})"

private structure EdgeIn where
  u : Nat
  v : Nat
  t : TranslationVec
  deriving Repr

private def parseTranslationE (j : Lean.Json) (ctx : String) : Except String TranslationVec := do
  let xs ← jsonArrE j ctx
  if xs.size != 3 then
    throw s!"{ctx}: expected 3-vector, got size={xs.size}"
  let x ← jsonIntE xs[0]! s!"{ctx}[0]"
  let y ← jsonIntE xs[1]! s!"{ctx}[1]"
  let z ← jsonIntE xs[2]! s!"{ctx}[2]"
  return { x := x, y := y, z := z }

private def parseEdgeInE (j : Lean.Json) (ctx : String) : Except String EdgeIn := do
  let u ← jsonNatE (← getObjValE j "u" ctx) s!"{ctx}.u"
  let v ← jsonNatE (← getObjValE j "v" ctx) s!"{ctx}.v"
  let t ← parseTranslationE (← getObjValE j "t" ctx) s!"{ctx}.t"
  return { u := u, v := v, t := t }

private structure GraphIn where
  id? : Option String := none
  labels : Array String
  edges : Array EdgeIn
  deriving Repr

private def parseGraphInE (j : Lean.Json) (ctx : String) : Except String GraphIn := do
  let labelsJ ← getObjValE j "labels" ctx
  let labelsA ← jsonArrE labelsJ s!"{ctx}.labels"
  let labels : Array String ← labelsA.mapM (fun x => jsonStrE x s!"{ctx}.labels[*]")
  let edgesJ ← getObjValE j "edges" ctx
  let edgesA ← jsonArrE edgesJ s!"{ctx}.edges"
  let edges : Array EdgeIn ←
    edgesA.mapIdxM (fun i x => parseEdgeInE x s!"{ctx}.edges[{i}]")
  return { id? := getObjValOptStr j "id", labels := labels, edges := edges }

private def symbolsToElementsE (syms : Array String) : Except String (Array Element) := do
  let mut out : Array Element := #[]
  for s in syms do
    match HeytingLean.Chem.PeriodicTable.ofSymbol? s with
    | some e => out := out.push e
    | none => throw s!"Unknown element symbol: {s}"
  return out

private def buildCGraphE (g : GraphIn) : Except String CGraph := do
  let n := g.labels.size
  let elems ← symbolsToElementsE g.labels
  let mut es : Array CEdge := #[]
  for e in g.edges do
    if e.u >= n then
      throw s!"edge.u out of range: u={e.u}, n={n}"
    if e.v >= n then
      throw s!"edge.v out of range: v={e.v}, n={n}"
    es := es.push { u := e.u, v := e.v, t := e.t }
  return { labels := elems, edges := es }

private def evalCGraph (id? : Option String) (canonMaxN : Nat) (canonMode : String) (g : CGraph) : IO Lean.Json := do
  let n := g.n
  let t0 ← IO.monoMsNow
  let enc := encodeC g
  let t1 ← IO.monoMsNow
  let mut canonPrimary? : Option String := none
  let mut canonFast? : Option String := none
  let mut canonErr? : Option String := none
  let mut canonFastErr? : Option String := none
  let mut canonFastMs : Nat := 0
  let mut canonSkipped : Bool := false
  if n > canonMaxN then
    canonSkipped := true
  else
    if canonMode = "fast" || canonMode = "both" then
      let tf0 ← IO.monoMsNow
      match canonEncodeCLabelSorted g with
      | .ok c => canonFast? := some c
      | .error err => canonFastErr? := some err
      let tf1 ← IO.monoMsNow
      canonFastMs := tf1 - tf0
    if canonMode = "full" || canonMode = "both" then
      match canonEncodeC g with
      | .ok c => canonPrimary? := some c
      | .error err => canonErr? := some err
    else
      canonPrimary? := canonFast?
  let t2 ← IO.monoMsNow
  let canonMs : Nat := if canonSkipped then 0 else (t2 - t1)

  let dec := decodeC? enc
  let canonKey? : Option String :=
    match canonPrimary?, canonFast? with
    | some c, _ => some c
    | none, some c => some c
    | none, none => none
  let primaryFn : CGraph → Except String String :=
    if canonMode = "fast" then canonEncodeCLabelSorted else canonEncodeC
  let (decOk, decErr?, rtCanonOk) :=
    match dec, canonPrimary? with
    | .ok g', some c =>
        match primaryFn g' with
        | .ok c' => (true, none, decide (c' = c))
        | .error err => (false, some s!"roundtrip canon error: {err}", false)
    | .ok _g', none =>
        (true, none, false)
    | .error err, _ =>
        (false, some err, false)

  let base : List (String × Lean.Json) :=
    [ ("n", Lean.Json.num (Lean.JsonNumber.fromNat n))
    , ("m", Lean.Json.num (Lean.JsonNumber.fromNat g.edges.size))
    , ("encode", Lean.Json.str enc)
    , ("decode_ok", Lean.Json.bool decOk)
    , ("roundtrip_canon_ok", Lean.Json.bool rtCanonOk)
    , ("encode_ms", Lean.Json.num (Lean.JsonNumber.fromNat (t1 - t0)))
    , ("canon_ms", Lean.Json.num (Lean.JsonNumber.fromNat canonMs))
    , ("canon_skipped", Lean.Json.bool canonSkipped)
    ]

  let base :=
    match canonPrimary? with
    | none => base
    | some c => base ++ [("canon", Lean.Json.str c)]

  let base :=
    match canonKey? with
    | none => base
    | some c => base ++ [("canon_key", Lean.Json.str c)]

  let base :=
    if canonMode = "both" || canonMode = "fast" then
      match canonFast? with
      | some c =>
          let extra : List (String × Lean.Json) :=
            [ ("canon_fast", Lean.Json.str c)
            , ("canon_fast_ms", Lean.Json.num (Lean.JsonNumber.fromNat canonFastMs))
            ]
          let extra :=
            if canonMode = "both" then
              match canonPrimary? with
              | some cFull => extra ++ [("canon_fast_matches_full", Lean.Json.bool (decide (c = cFull)))]
              | none => extra
            else
              extra
          base ++ extra
      | none =>
          match canonFastErr? with
          | some err => base ++ [("canon_fast_error", Lean.Json.str err), ("canon_fast_ms", Lean.Json.num (Lean.JsonNumber.fromNat canonFastMs))]
          | none => base ++ [("canon_fast_ms", Lean.Json.num (Lean.JsonNumber.fromNat canonFastMs))]
    else
      base

  let base :=
    match decErr? with
    | none => base
    | some err => base ++ [("decode_error", Lean.Json.str err)]

  let base :=
    match canonErr? with
    | none => base
    | some err => base ++ [("canon_error", Lean.Json.str err)]

  let base :=
    match id? with
    | none => base
    | some s => [("id", Lean.Json.str s)] ++ base

  return Lean.Json.mkObj base

private def evalLine (canonMaxN : Nat) (canonMode : String) (line : String) : IO Lean.Json := do
  let trimmed := line.trim
  if trimmed = "" then
    return Lean.Json.mkObj [("skip", Lean.Json.bool true)]

  match Lean.Json.parse trimmed with
  | .error e =>
      -- Fallback: treat as a raw SLICES string.
      let s := trimmed
      match decodeC? s with
      | .ok g =>
          evalCGraph none canonMaxN canonMode g
      | .error err =>
          return Lean.Json.mkObj
            [ ("decode_ok", Lean.Json.bool false)
            , ("decode_error", Lean.Json.str s!"json_parse_error={e}; slices_decode_error={err}")
            ]
  | .ok j =>
      -- JSON mode: either {"slices": "..."} or {"labels": [...], "edges": [...]}.
      match j.getObjVal? "slices" with
      | .ok sj =>
          match jsonStrE sj "slices" with
          | .ok s =>
              match decodeC? s with
              | .ok g =>
                  let id? := getObjValOptStr j "id"
                  evalCGraph id? canonMaxN canonMode g
              | .error err =>
                  return Lean.Json.mkObj
                    [ ("id", match getObjValOptStr j "id" with | some s => Lean.Json.str s | none => Lean.Json.null)
                    , ("decode_ok", Lean.Json.bool false)
                    , ("decode_error", Lean.Json.str err)
                    ]
          | .error err =>
              return Lean.Json.mkObj [("decode_ok", Lean.Json.bool false), ("decode_error", Lean.Json.str err)]
      | .error _ =>
          match parseGraphInE j "graph" with
          | .error err =>
              return Lean.Json.mkObj [("decode_ok", Lean.Json.bool false), ("decode_error", Lean.Json.str err)]
          | .ok gIn =>
              match buildCGraphE gIn with
              | .error err =>
                  return Lean.Json.mkObj
                    [ ("id", match gIn.id? with | some s => Lean.Json.str s | none => Lean.Json.null)
                    , ("decode_ok", Lean.Json.bool false)
                    , ("decode_error", Lean.Json.str err)
                    ]
              | .ok g =>
                  evalCGraph gIn.id? canonMaxN canonMode g

private def usage : String :=
  String.intercalate "\n"
    [ "usage:"
    , "  slices_bench --stdin"
    , "  slices_bench --input <path.jsonl>"
    , "  slices_bench --canon-mode full|fast|both"
    , ""
    , "input (one per line):"
    , "  - JSON object with {\"labels\": [\"C\", ...], \"edges\": [{\"u\":0,\"v\":1,\"t\":[0,0,0]}, ...]}"
    , "  - OR JSON object with {\"slices\": \"...\"}"
    , "  - OR a raw SLICES string (non-JSON line)"
    ]

private def readLinesFromFile (path : System.FilePath) : IO (Except String (Array String)) := do
  try
    let s ← IO.FS.readFile path
    return .ok (s.splitOn "\n" |>.toArray)
  catch e =>
    return .error s!"read error at {path}: {e}"

def main (args : List String) : IO UInt32 := do
  if args.any (· = "--help") then
    IO.println usage
    return 0

  let inputPath? : Option String :=
    let rec goInput : List String → Option String
      | [] => none
      | a :: b :: rest => if a = "--input" then some b else goInput (b :: rest)
      | _ :: [] => none
    goInput args

  let canonMaxN : Nat :=
    let rec goCanon : List String → Option Nat
      | [] => none
      | a :: b :: rest =>
          if a = "--canon-max-n" then
            b.toNat?
          else
            goCanon (b :: rest)
      | _ :: [] => none
    match goCanon args with
    | some n => n
    | none => 9

  let canonMode : String :=
    let rec goMode : List String → Option String
      | [] => none
      | a :: b :: rest =>
          if a = "--canon-mode" then
            some b
          else
            goMode (b :: rest)
      | _ :: [] => none
    match goMode args with
    | some m =>
        if m = "full" || m = "fast" || m = "both" then m else "full"
    | none => "full"

  match inputPath? with
  | none =>
      let h ← IO.getStdin
      while true do
        try
          let line ← h.getLine
          if line = "" then
            break
          let out ← evalLine canonMaxN canonMode line
          outputJson out
        catch _ =>
          break
  | some p =>
      let lines ←
        match (← readLinesFromFile p) with
        | .ok xs => pure xs
        | .error err =>
            IO.eprintln err
            return 1
      for line in lines do
        let out ← evalLine canonMaxN canonMode line
        outputJson out
  return 0

end HeytingLean.CLI

-- Lake executables expect a top-level `main`. We delegate to the namespaced implementation.
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.main args
