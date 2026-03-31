import HeytingLean.MirandaDynamics.Thermal.SafetyPredicates

/-!
# MirandaDynamics.Thermal.Autotune

Lean-side types for thermodynamics-aware autotuning certificates.

Phase 1 goal:
- Provide a stable, Lean-native vocabulary for "knobs, constraints, measurements, verdict"
  so runtime tooling can attach theorem references and future agents can search for the
  concepts in the namespace.

We keep this file definition-heavy (no proof placeholders) and intentionally avoid tricky
theorems about `Float` order (NaN/IEEE concerns are documented in `SafetyPredicates`).
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal

structure AutotuneConstraints where
  /-- Optional maximum GPU temperature (C). -/
  maxGpuTempC? : Option Float := none
  /-- Optional maximum GPU power (W). -/
  maxGpuPowerW? : Option Float := none
  deriving Repr

structure AutotuneMeasurements where
  durationS : Float
  energyJ : Float
  avgPowerW : Float
  /-- Optional observed max GPU temperature (C). -/
  maxGpuTempC? : Option Float := none
  /-- Optional observed max GPU power (W). -/
  maxGpuPowerW? : Option Float := none
  deriving Repr

structure AutotuneVerdict where
  ok : Bool
  /-- Human/debug readable check IDs (e.g. "constraint.max_gpu_temp_C"). -/
  checks : List String := []
  deriving Repr

/-- Check constraints against measurements (Bool-level, runtime-friendly). -/
def checkConstraints (c : AutotuneConstraints) (m : AutotuneMeasurements) : AutotuneVerdict :=
  let okTemp :=
    match c.maxGpuTempC?, m.maxGpuTempC? with
    | some lim, some obs => obs < lim
    | _, _ => true
  let okPower :=
    match c.maxGpuPowerW?, m.maxGpuPowerW? with
    | some lim, some obs => obs < lim
    | _, _ => true
  let ok := okTemp && okPower
  let checks :=
    (if okTemp then [] else ["constraint.max_gpu_temp_C"]) ++
    (if okPower then [] else ["constraint.max_gpu_power_W"])
  { ok := ok, checks := checks }

/-- A thin bridge: if you want to use the default `gpu_safe` predicate from `SafetyPredicates`,
call this helper (Bool-level). -/
def gpuSafeDefault? (tempC? : Option Float) : Bool :=
  match tempC? with
  | none => true
  | some t => isSafeTempDecide ThermalBounds.gpuDefault t

end Thermal
end MirandaDynamics
end HeytingLean
