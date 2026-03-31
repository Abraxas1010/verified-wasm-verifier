import Lean
import Lean.Data.Json
import Std

import HeytingLean.MirandaDynamics.Seismic.Categorical

/-!
# MirandaDynamics.Seismic: categorical interpretation of validation

This module interprets the executable validation output in terms of a simple
"predicted vs observed" kernel-style picture.

Given a validation pair, define:
- `P` = the predicted reachability claim (`should_reach`).
- `j(P)` = the observed/verifiable reachability claim (`did_reach`).
- `gap` = `P ∧ ¬j(P)` (true in the prediction model but not verified by observation).

This layer is intended to produce *meaningful* summaries in human-readable form,
while remaining compatible with machine-readable JSON output.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Seismic
namespace CategoricalValidation

open Lean
open Std

structure ValidationPair where
  event_id : String
  station : String
  should_reach : Bool
  did_reach : Bool
  within_tolerance : Bool
  waveform_ok : Bool
  timing_error_ms : Option Int
  deriving Repr

structure StandardMetrics where
  total_pairs : Nat
  predicted_reach : Nat
  predicted_no_reach : Nat
  observed_reach : Nat
  observed_no_reach : Nat
  true_positive : Nat
  true_negative : Nat
  false_positive : Nat
  false_negative : Nat
  accuracy : Float
  false_negative_rate : Float
  false_positive_rate : Float
  mean_abs_timing_error_sec : Float
  std_abs_timing_error_sec : Float
  max_abs_timing_error_sec : Float
  deriving Repr

private def mean (xs : Array Float) : Float :=
  if xs.isEmpty then
    0.0
  else
    xs.foldl (· + ·) 0.0 / xs.size.toFloat

private def std (xs : Array Float) : Float :=
  if xs.size < 2 then
    0.0
  else
    let m := mean xs
    let var := xs.foldl (fun acc x => acc + (x - m) * (x - m)) 0.0 / xs.size.toFloat
    Float.sqrt var

private def roundTo (x : Float) (decimals : Nat) : Float :=
  let factor := Float.pow 10.0 (Float.ofNat decimals)
  (x * factor).round / factor

private def fmt (x : Float) (decimals : Nat) : String :=
  (roundTo x decimals).toString

def computeStandardMetrics (pairs : Array ValidationPair) : StandardMetrics :=
  let valid := pairs.filter (·.waveform_ok)
  let predicted_reach := valid.filter (·.should_reach) |>.size
  let predicted_no := valid.size - predicted_reach
  let observed_reach := valid.filter (·.did_reach) |>.size
  let observed_no := valid.size - observed_reach

  let tp := valid.filter (fun p => p.should_reach && p.did_reach) |>.size
  let tn := valid.filter (fun p => (!p.should_reach) && (!p.did_reach)) |>.size
  let fp := valid.filter (fun p => (!p.should_reach) && p.did_reach) |>.size
  let fn := valid.filter (fun p => p.should_reach && (!p.did_reach)) |>.size

  let total := valid.size
  let acc : Float :=
    if total = 0 then 0.0 else (tp + tn).toFloat / total.toFloat
  let fnr : Float :=
    if predicted_reach = 0 then 0.0 else fn.toFloat / predicted_reach.toFloat
  let fpr : Float :=
    if predicted_no = 0 then 0.0 else fp.toFloat / predicted_no.toFloat

  let absErrs : Array Float :=
    valid.filterMap (fun p =>
      match p.timing_error_ms with
      | none => none
      | some ms =>
          if p.should_reach && p.did_reach then
            some (Float.ofInt (Int.natAbs ms) / 1000.0)
          else
            none)

  let meanAbs := mean absErrs
  let stdAbs := std absErrs
  let maxAbs := absErrs.foldl max 0.0

  {
    total_pairs := total
    predicted_reach := predicted_reach
    predicted_no_reach := predicted_no
    observed_reach := observed_reach
    observed_no_reach := observed_no
    true_positive := tp
    true_negative := tn
    false_positive := fp
    false_negative := fn
    accuracy := acc
    false_negative_rate := fnr
    false_positive_rate := fpr
    mean_abs_timing_error_sec := meanAbs
    std_abs_timing_error_sec := stdAbs
    max_abs_timing_error_sec := maxAbs
  }

def formatStandardReport (m : StandardMetrics) : String :=
  s!"\
Data Summary:\n\
- Event-station pairs evaluated: {m.total_pairs}\n\
\n\
Reachability Prediction:\n\
- Predicted reach: {m.predicted_reach}\n\
- Predicted no-reach: {m.predicted_no_reach}\n\
\n\
Observation Results:\n\
- Observed reach (threshold crossing detected): {m.observed_reach}\n\
- Observed no-reach: {m.observed_no_reach}\n\
\n\
Confusion Matrix:\n\
- True positive: {m.true_positive}\n\
- True negative: {m.true_negative}\n\
- False positive: {m.false_positive}\n\
- False negative: {m.false_negative}\n\
\n\
Metrics:\n\
- Accuracy: {fmt (100.0 * m.accuracy) 2}%\n\
- False negative rate: {fmt (100.0 * m.false_negative_rate) 2}%\n\
- False positive rate: {fmt (100.0 * m.false_positive_rate) 2}%\n\
\n\
Timing (for true positives):\n\
- Mean |predicted - observed|: {fmt m.mean_abs_timing_error_sec 1} seconds\n\
- Std deviation: {fmt m.std_abs_timing_error_sec 1} seconds\n\
- Max error: {fmt m.max_abs_timing_error_sec 1} seconds\n"

structure CategoricalSummary where
  total : Nat
  nucleus_identity : Nat
  nucleus_contracted : Nat
  nucleus_expanded : Nat
  both_false : Nat
  mean_nucleus_width_ms : Float
  heyting_gap_rate : Float
  fixed_point : Bool
  deriving Repr

def summarizeCategorically (pairs : Array ValidationPair) : CategoricalSummary :=
  let valid := pairs.filter (·.waveform_ok)

  let nucleus_identity := valid.filter (fun p => p.should_reach && p.did_reach) |>.size
  let nucleus_contracted := valid.filter (fun p => p.should_reach && (!p.did_reach)) |>.size
  let nucleus_expanded := valid.filter (fun p => (!p.should_reach) && p.did_reach) |>.size
  let both_false := valid.filter (fun p => (!p.should_reach) && (!p.did_reach)) |>.size

  let timingAbsMs : Array Float :=
    valid.filterMap (fun p =>
      match p.timing_error_ms with
      | none => none
      | some ms =>
          if p.should_reach && p.did_reach then
            some (Float.ofInt (Int.natAbs ms))
          else
            none)
  let meanWidthMs := mean timingAbsMs

  let reaches_true := valid.filter (·.should_reach) |>.size
  let gapRate := if reaches_true = 0 then 0.0 else nucleus_contracted.toFloat / reaches_true.toFloat

  let fixedPoint := (nucleus_contracted = 0) && (nucleus_expanded = 0)

  {
    total := valid.size
    nucleus_identity := nucleus_identity
    nucleus_contracted := nucleus_contracted
    nucleus_expanded := nucleus_expanded
    both_false := both_false
    mean_nucleus_width_ms := meanWidthMs
    heyting_gap_rate := gapRate
    fixed_point := fixedPoint
  }

def generateCategoricalReport (summary : CategoricalSummary) : String :=
  s!"\
Categorical interpretation (kernel-style):\n\
\n\
Treat `P` as predicted reachability and `j(P)` as observed/verifiable reachability.\n\
\n\
- Total pairs (waveform_ok): {summary.total}\n\
- j(P) = P (reach observed when predicted): {summary.nucleus_identity}\n\
- j(P) < P (gap / false negative): {summary.nucleus_contracted}\n\
- j(P) > P (false positive): {summary.nucleus_expanded}\n\
- both false (no reach predicted nor observed): {summary.both_false}\n\
\n\
- Mean nucleus width |Δt|: {fmt (summary.mean_nucleus_width_ms / 1000.0) 1} seconds\n\
- Heyting gap rate P ∧ ¬j(P): {fmt (100.0 * summary.heyting_gap_rate) 2}%\n\
- Fixed point (sets equal): {summary.fixed_point}\n"

def StandardMetrics.toJson (m : StandardMetrics) : Json :=
  Json.mkObj
    [ ("total_pairs", Json.num (JsonNumber.fromNat m.total_pairs))
    , ("predicted_reach", Json.num (JsonNumber.fromNat m.predicted_reach))
    , ("predicted_no_reach", Json.num (JsonNumber.fromNat m.predicted_no_reach))
    , ("observed_reach", Json.num (JsonNumber.fromNat m.observed_reach))
    , ("observed_no_reach", Json.num (JsonNumber.fromNat m.observed_no_reach))
    , ("true_positive", Json.num (JsonNumber.fromNat m.true_positive))
    , ("true_negative", Json.num (JsonNumber.fromNat m.true_negative))
    , ("false_positive", Json.num (JsonNumber.fromNat m.false_positive))
    , ("false_negative", Json.num (JsonNumber.fromNat m.false_negative))
    , ("accuracy", Json.str (fmt m.accuracy 8))
    , ("false_negative_rate", Json.str (fmt m.false_negative_rate 8))
    , ("false_positive_rate", Json.str (fmt m.false_positive_rate 8))
    , ("mean_abs_timing_error_sec", Json.str (fmt m.mean_abs_timing_error_sec 6))
    , ("std_abs_timing_error_sec", Json.str (fmt m.std_abs_timing_error_sec 6))
    , ("max_abs_timing_error_sec", Json.str (fmt m.max_abs_timing_error_sec 6))
    ]

def CategoricalSummary.toJson (m : CategoricalSummary) : Json :=
  Json.mkObj
    [ ("total", Json.num (JsonNumber.fromNat m.total))
    , ("nucleus_identity", Json.num (JsonNumber.fromNat m.nucleus_identity))
    , ("nucleus_contracted", Json.num (JsonNumber.fromNat m.nucleus_contracted))
    , ("nucleus_expanded", Json.num (JsonNumber.fromNat m.nucleus_expanded))
    , ("both_false", Json.num (JsonNumber.fromNat m.both_false))
    , ("mean_nucleus_width_ms", Json.str (fmt m.mean_nucleus_width_ms 3))
    , ("heyting_gap_rate", Json.str (fmt m.heyting_gap_rate 8))
    , ("fixed_point", Json.bool m.fixed_point)
    ]

end CategoricalValidation
end Seismic
end MirandaDynamics
end HeytingLean
