import Lean
import Lean.Data.Json
import Std

import HeytingLean.CLI.Certified.Json
import HeytingLean.MirandaDynamics.Seismic.Validation
import HeytingLean.MirandaDynamics.Seismic.CategoricalValidation

/-!
# Seismic validation demo (offline)

This executable reads a JSON validation bundle (produced by `scripts/seismic_bridge.py`) and runs
an STA/LTA arrival detector on each `(event,station)` waveform window.

It is intentionally offline and deterministic so it can be used in QA runs.

Usage:

`lake exe seismic_validate_demo` (uses `data/seismic/sample_bundle.json`)

or

`lake exe seismic_validate_demo -- --input path/to/bundle.json`

It also accepts a positional path:

`lake exe seismic_validate_demo -- path/to/bundle.json`
-/

namespace HeytingLean
namespace CLI

open Lean
open Std

def defaultBundlePath : String :=
  "data/seismic/sample_bundle.json"

def defaultBundlePathAlt : String :=
  "../data/seismic/sample_bundle.json"

def fileExists (p : String) : IO Bool := do
  let fp : System.FilePath := p
  return (← fp.pathExists)

def findDefaultBundlePath : IO String := do
  if (← fileExists defaultBundlePath) then
    return defaultBundlePath
  if (← fileExists defaultBundlePathAlt) then
    return defaultBundlePathAlt
  return defaultBundlePath

def readInputJson (args : List String) : IO (Except String Json) := do
  let useStdin := args.contains "--stdin"

  let rec findInputFile : List String → Option String
    | "--input" :: f :: _ => some f
    | f :: rest =>
        if f.startsWith "--" then
          findInputFile rest
        else
          some f
    | [] => none

  let input ←
    match findInputFile args with
    | some f =>
        try
          IO.FS.readFile f
        catch e =>
          return .error s!"failed to read {f}: {e.toString}"
    | none =>
        if useStdin then
          (do
            let h ← IO.getStdin
            h.readToEnd)
        else
          return .error "no input provided (use --input FILE or --stdin)"

  match Json.parse input with
  | .ok j => pure (.ok j)
  | .error e => pure (.error s!"json error: {e}")

def getFloat? (j : Json) (k : String) : Option Float :=
  match j.getObjVal? k with
  | .ok v =>
      match v.getNum? with
      | .ok n => some n.toFloat
      | .error _ => none
  | .error _ => none

def getFloatArray? (j : Json) (k : String) : Option (Array Float) :=
  match j.getObjVal? k with
  | .ok (.arr xs) =>
      Id.run do
        let mut out : Array Float := #[]
        for x in xs do
          match x.getNum? with
          | .ok f =>
              out := out.push f.toFloat
          | .error _ =>
              return none
        return some out
  | _ => none

structure Bundle where
  metaJson : Json
  predictionsJson : Json
  waveformsJson : Json

structure ValidationOutput where
  outJson : Json
  pairs : Array HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.ValidationPair
  std : HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.StandardMetrics
  cat : HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.CategoricalSummary

def parseBundle (j : Json) : Except String Bundle := do
  let metaJson ← match j.getObjVal? "metadata" with
    | .ok v => pure v
    | .error _ => throw "missing field: metadata"
  let preds ← match j.getObjVal? "predictions" with
    | .ok v => pure v
    | .error _ => throw "missing field: predictions"
  let wfs ← match j.getObjVal? "waveforms" with
    | .ok v => pure v
    | .error _ => throw "missing field: waveforms"
  pure { metaJson := metaJson, predictionsJson := preds, waveformsJson := wfs }

def getBool? (j : Json) (k : String) : Option Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => some b
  | _ => none

def getString? (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

def parseDetectionParams (metaJ : Json) : Except String (Float × Float × Float × Float) := do
  let det ← match metaJ.getObjVal? "detection" with
    | .ok v => pure v
    | .error _ => throw "metadata.detection missing"
  let sta ← match getFloat? det "sta_sec" with
    | some f => pure f
    | none => throw "metadata.detection.sta_sec missing"
  let lta ← match getFloat? det "lta_sec" with
    | some f => pure f
    | none => throw "metadata.detection.lta_sec missing"
  let thr ← match getFloat? det "snr_threshold" with
    | some f => pure f
    | none => throw "metadata.detection.snr_threshold missing"
  let tol ← match getFloat? metaJ "tolerance_sec" with
    | some f => pure f
    | none => throw "metadata.tolerance_sec missing"
  pure (sta, lta, thr, tol)

def mkKey (eventId station : String) : String :=
  eventId ++ "|" ++ station

def validateBundle (b : Bundle) : Except String ValidationOutput := do
  let (staSec, ltaSec, thr, tolSec) ← parseDetectionParams b.metaJson
  let tolMs : Int := Int.ofNat (UInt64.toNat ((tolSec * 1000.0).toUInt64))

  -- Build prediction map.
  let predArr ←
    match b.predictionsJson with
    | .arr xs => pure xs
    | _ => throw "predictions must be an array"
  let mut predMap : Std.HashMap String Json := {}
  for p in predArr.toList do
    match p with
    | .obj _ =>
        let some eid := getString? p "event_id" | continue
        let some st := getString? p "station" | continue
        predMap := predMap.insert (mkKey eid st) p
    | _ =>
        continue

  let wfArr ←
    match b.waveformsJson with
    | .arr xs => pure xs
    | _ => throw "waveforms must be an array"

  let mut results : Array Json := #[]
  let mut pairs : Array HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.ValidationPair := #[]
  let mut nTotal : Nat := 0
  let mut nWithWaveform : Nat := 0
  let mut nDetected : Nat := 0

  for w in wfArr.toList do
    nTotal := nTotal + 1
    let some eid := getString? w "event_id" | continue
    let some st := getString? w "station" | continue
    let key := mkKey eid st
    let pred? := predMap.get? key
    let pred := match pred? with | some p => p | none => Json.mkObj []
    let shouldReach :=
      match getBool? pred "should_reach" with
      | some b => b
      | none => true
    let predMs :=
      match HeytingLean.CLI.Certified.getInt? pred "predicted_p_arrival_ms" with
      | some i => i
      | none => 0

    -- If the waveform has an error (missing data), record and continue.
    match w.getObjVal? "error" with
    | .ok (.str err) =>
        results := results.push <|
          Json.mkObj
            [ ("event_id", Json.str eid)
            , ("station", Json.str st)
            , ("should_reach", Json.bool shouldReach)
            , ("predicted_arrival_ms", Json.num (JsonNumber.fromInt predMs))
            , ("waveform_ok", Json.bool false)
            , ("error", Json.str err)
            ]
    | _ =>
        let some startMs := HeytingLean.CLI.Certified.getInt? w "start_time_ms" | continue
        let some sr := getFloat? w "sample_rate_hz" | continue
        let some samples := getFloatArray? w "samples" | continue
        nWithWaveform := nWithWaveform + 1

        -- Tighten the search window around the predicted P arrival to reduce false triggers.
        let dtMs : Float := 1000.0 / sr
        let searchStartMs : Int := predMs - (Int.ofNat (60 * 1000))
        let searchStopMs : Int := predMs + (Int.ofNat (10 * 60 * 1000))
        let startIdx : Nat :=
          if searchStartMs <= startMs then
            0
          else
            UInt64.toNat (((Float.ofInt (searchStartMs - startMs)) / dtMs).toUInt64)
        let stopIdx : Nat :=
          if searchStopMs <= startMs then
            0
          else
            UInt64.toNat (((Float.ofInt (searchStopMs - startMs)) / dtMs).toUInt64)
        let stopIdx := min stopIdx samples.size
        let startIdx := min startIdx stopIdx
        let sub := samples.extract startIdx stopIdx
        let offsetMs : Float := (Float.ofNat startIdx) * dtMs
        let startMs' : Int := startMs + (Int.ofNat (UInt64.toNat offsetMs.toUInt64))
        let obsStartAtMs : Int := predMs - (Int.ofNat (10 * 1000))
        let obsRaw :=
          HeytingLean.MirandaDynamics.Seismic.observedArrivalMsSTA_LTA?
            startMs' sr sub staSec ltaSec thr (some obsStartAtMs)
        -- If the first trigger is far from the predicted P arrival, treat it as “no P arrival detected”
        -- (i.e. ignore surface-wave triggers). This keeps validation focused on P-wave reachability.
        let maxErrMs : Nat := 30 * 1000
        let obs :=
          match obsRaw with
          | none => none
          | some t =>
              if Int.natAbs (t - predMs) ≤ maxErrMs then
                some t
              else
                none
        let didReach := obs.isSome
        if didReach then
          nDetected := nDetected + 1
        let withinTol :=
          match obs with
          | none => false
          | some t => Int.natAbs (t - predMs) ≤ Int.natAbs tolMs
        let errMs : Json :=
          match obs with
          | none => Json.null
          | some t => Json.num (JsonNumber.fromInt (t - predMs))
        let timingErr : Option Int :=
          match obs with
          | none => none
          | some t => some (t - predMs)
        pairs := pairs.push
          { event_id := eid
            station := st
            should_reach := shouldReach
            did_reach := didReach
            within_tolerance := withinTol
            waveform_ok := true
            timing_error_ms := timingErr
          }
        results := results.push <|
          Json.mkObj
            [ ("event_id", Json.str eid)
            , ("station", Json.str st)
            , ("should_reach", Json.bool shouldReach)
            , ("predicted_arrival_ms", Json.num (JsonNumber.fromInt predMs))
            , ("observed_arrival_ms", match obs with | none => Json.null | some t => Json.num (JsonNumber.fromInt t))
            , ("timing_error_ms", errMs)
            , ("did_reach", Json.bool didReach)
            , ("within_tolerance", Json.bool withinTol)
            , ("waveform_ok", Json.bool true)
            ]

  let std := HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.computeStandardMetrics pairs
  let cat := HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.summarizeCategorically pairs
  let outJson :=
    Json.mkObj
      [ ("metadata", b.metaJson)
      , ("stats",
          Json.mkObj
            [ ("total_waveform_entries", Json.num (JsonNumber.fromNat nTotal))
            , ("waveform_ok", Json.num (JsonNumber.fromNat nWithWaveform))
            , ("detected", Json.num (JsonNumber.fromNat nDetected))
            ])
      , ("pairs", Json.arr results)
      , ("standard_metrics", HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.StandardMetrics.toJson std)
      , ("categorical_summary", HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.CategoricalSummary.toJson cat)
      ]

  pure { outJson := outJson, pairs := pairs, std := std, cat := cat }

def main (args : List String) : IO UInt32 := do
  let jsonOnly := args.contains "--json-only"
  let hasPositionalFile := args.any (fun a => !a.startsWith "--")
  let args' ←
    if args.contains "--input" || args.contains "--stdin" || hasPositionalFile then
      pure args
    else
      pure ["--input", (← findDefaultBundlePath)]

  let input ← readInputJson args'
  match input with
  | .error e =>
      IO.eprintln e
      return 1
  | .ok j =>
      match parseBundle j with
      | .error e =>
          IO.eprintln e
          return 1
      | .ok b =>
          match validateBundle b with
          | .error e =>
              IO.eprintln e
              return 1
          | .ok out =>
              if jsonOnly then
                IO.println out.outJson.pretty
              else
                IO.println "=== STANDARD VALIDATION METRICS ==="
                IO.println (HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.formatStandardReport out.std)
                IO.println ""
                IO.println "=== CATEGORICAL INTERPRETATION ==="
                IO.println (HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.generateCategoricalReport out.cat)
                IO.println ""
                IO.println "=== JSON OUTPUT ==="
                IO.println out.outJson.pretty
              return 0

end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.main args
