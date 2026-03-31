import HeytingLean.MirandaDynamics.Seismic.Basic

/-!
# MirandaDynamics.Seismic: validation definitions (offline)

This file defines a small, executable-friendly “arrival detection” function over a waveform.

The intent is:
- Python fetches real waveform windows (GeoCSV), producing a JSON bundle.
- A Lean executable consumes the bundle and runs the same detection logic.

This does not attempt high-quality picking; it is a simple threshold crossing.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Seismic

def absF (x : Float) : Float :=
  if x < 0 then -x else x

def sumAbs (samples : Array Float) (start len : Nat) : Float :=
  let stop := start + len
  let rec go (i : Nat) (acc : Float) : Float :=
    if h : i < samples.size then
      if i < stop then
        go (i + 1) (acc + absF (samples[i]'h))
      else
        acc
    else
      acc
  go start 0

def sumAbsRange (samples : Array Float) (start stop : Nat) : Float :=
  let stop := min stop samples.size
  let rec go (i : Nat) (acc : Float) : Float :=
    if i < stop then
      match samples[i]? with
      | some v =>
          -- Use a simple first-difference to remove DC offset / slow drift.
          let dv :=
            if i = 0 then
              0
            else
              match samples[i-1]? with
              | some vPrev => v - vPrev
              | none => 0
          -- Energy-style envelope (squared first difference).
          go (i + 1) (acc + dv * dv)
      | none => acc
    else
      acc
  go start 0

/-- Detect an arrival index using a classic STA/LTA ratio on the absolute-value envelope.

Returns the first sample index `i` where

`(STA(i) / LTA(i)) ≥ threshold`.

`STA(i)` is the average of the last `staN` samples ending at `i`.
`LTA(i)` is the average of the last `ltaN` samples ending at `i`.

This is intentionally simple; it is good enough for a validation demo.
-/
def detectSTA_LTA? (samples : Array Float) (threshold : Float) (staN ltaN : Nat)
    (startAt : Nat := 0) (holdN : Nat := 5) : Option Nat :=
  let size := samples.size
  let staN := max 1 staN
  let ltaN := max (staN + 1) ltaN
  if size < ltaN then
    none
  else
    let i0 := max (ltaN - 1) startAt
    let holdN := max 1 holdN
    let rec loop (i : Nat) (streak : Nat) : Option Nat :=
      if h : i < size then
        let ltaSum := sumAbsRange samples (i + 1 - ltaN) (i + 1)
        let staSum := sumAbsRange samples (i + 1 - staN) (i + 1)
        let ltaAvg := ltaSum / (Float.ofNat ltaN)
        let staAvg := staSum / (Float.ofNat staN)
        let ratio := if ltaAvg <= 0 then 0 else staAvg / ltaAvg
        if ratio >= threshold then
          let streak' := streak + 1
          if streak' >= holdN then
            -- return the first index of the consecutive run
            some (i + 1 - holdN)
          else
            loop (i + 1) streak'
        else
          loop (i + 1) 0
      else
        none
    loop i0 0

def observedArrivalMsSTA_LTA?
    (start_time_ms : Int) (sample_rate_hz : Float) (samples : Array Float)
    (sta_sec lta_sec threshold : Float) (startAtMs? : Option Int := none) : Option Int :=
  if sample_rate_hz <= 0 then
    none
  else
    let dt_ms : Float := 1000.0 / sample_rate_hz
    let staN : Nat := max 1 (UInt64.toNat ((sta_sec * sample_rate_hz).toUInt64))
    let ltaN : Nat := max (staN + 1) (UInt64.toNat ((lta_sec * sample_rate_hz).toUInt64))
    let startAt : Nat :=
      match startAtMs? with
      | none => 0
      | some t =>
          if t <= start_time_ms then
            0
          else
            UInt64.toNat (((Float.ofInt (t - start_time_ms)) / dt_ms).toUInt64)
    match detectSTA_LTA? samples threshold staN ltaN startAt with
    | none => none
    | some i =>
        let offset_ms : Float := (Float.ofNat i) * dt_ms
        some <| start_time_ms + (Int.ofNat (UInt64.toNat offset_ms.toUInt64))

end Seismic
end MirandaDynamics
end HeytingLean
