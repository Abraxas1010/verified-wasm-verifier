import HeytingLean.MirandaDynamics.Thermal.Basic

/-!
# MirandaDynamics.Thermal: safety predicates

This file defines the core safety predicates for thermal verification:

- `ThermalBounds`: configurable temperature thresholds per component
- `SafeTemp`: predicate asserting a temperature is below critical threshold
- `SafeRate`: predicate asserting temperature rate of change is bounded
- `SafeReading`: predicate asserting all zones in a reading are safe

These predicates are designed for binding with runtime thermal data from
the DGX Spark dashboard, enabling formal verification of safety invariants.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal

/-- Safety bounds per component type.

Default values based on DGX Spark thermal characteristics.
-/
structure ThermalBounds where
  criticalC : Float := 105.0    -- Critical threshold (must never exceed)
  warningC : Float := 95.0      -- Warning threshold (should trigger alerts)
  targetC : Float := 75.0       -- Target operating temperature
  maxRateC_per_s : Float := 5.0 -- Maximum safe rate of change (°C/s)
  deriving Repr

namespace ThermalBounds

/-- Default bounds for X925 performance cores. -/
def x925Default : ThermalBounds :=
  { criticalC := 105.0, warningC := 95.0, targetC := 75.0, maxRateC_per_s := 5.0 }

/-- Default bounds for A725 efficiency cores. -/
def a725Default : ThermalBounds :=
  { criticalC := 100.0, warningC := 90.0, targetC := 70.0, maxRateC_per_s := 4.0 }

/-- Default bounds for GPU. -/
def gpuDefault : ThermalBounds :=
  { criticalC := 100.0, warningC := 90.0, targetC := 80.0, maxRateC_per_s := 8.0 }

/-- Default bounds for SoC peripherals. -/
def socDefault : ThermalBounds :=
  { criticalC := 95.0, warningC := 85.0, targetC := 65.0, maxRateC_per_s := 3.0 }

/-- Default bounds for NVMe storage. -/
def nvmeDefault : ThermalBounds :=
  { criticalC := 85.0, warningC := 75.0, targetC := 55.0, maxRateC_per_s := 2.0 }

/-- Default bounds for network adapters. -/
def networkDefault : ThermalBounds :=
  { criticalC := 90.0, warningC := 80.0, targetC := 60.0, maxRateC_per_s := 2.0 }

/-- Get default bounds for a core class. -/
def forCoreClass (c : CoreClass) : ThermalBounds :=
  match c with
  | .x925_performance => x925Default
  | .a725_efficiency => a725Default
  | .gpu_compute => gpuDefault
  | .soc_peripheral => socDefault
  | .storage => nvmeDefault
  | .network => networkDefault

end ThermalBounds

/-! ## Core Safety Predicates -/

/-- Core predicate: temperature is below critical threshold.

This is the fundamental safety invariant for thermal monitoring.
-/
def SafeTemp (bounds : ThermalBounds) (tempC : Float) : Prop :=
  tempC < bounds.criticalC

/-- Predicate: temperature is in warning zone (above warning, below critical). -/
def WarningTemp (bounds : ThermalBounds) (tempC : Float) : Prop :=
  bounds.warningC ≤ tempC ∧ tempC < bounds.criticalC

/-- Predicate: temperature is in optimal zone (at or below target). -/
def OptimalTemp (bounds : ThermalBounds) (tempC : Float) : Prop :=
  tempC ≤ bounds.targetC

/-- Predicate: temperature rate of change is within safe bounds.

Rapid temperature changes can indicate thermal runaway or cooling failure.
-/
def SafeRate (bounds : ThermalBounds) (rateCPerS : Float) : Prop :=
  rateCPerS.abs < bounds.maxRateC_per_s

/-- Predicate: a thermal sample is safe (temperature within bounds). -/
def SafeSample (sample : ThermalSample) : Prop :=
  let bounds := ThermalBounds.forCoreClass sample.zone.coreClass
  SafeTemp bounds sample.tempC

/-- Predicate: all samples in a thermal reading are safe. -/
def SafeReading (reading : ThermalReading) : Prop :=
  ∀ i : Fin reading.samples.size, SafeSample (reading.samples[i])

/-- Predicate: a thermal state has all zones within safe bounds. -/
def SafeState (s : ThermalState) : Prop :=
  ∀ p ∈ s.zones, SafeTemp ThermalBounds.x925Default p.2
  -- Note: In practice, bounds should be looked up per zone

/-!
## Safety Theorems

We intentionally avoid proving general order-theoretic lemmas about `Float` here.
IEEE semantics (notably NaN) break many expected properties (e.g. transitivity),
so unconditional theorems are often false.

If/when we need such lemmas for a specific workflow, we should restate them with
explicit hypotheses like `¬ tempC.isNaN` (and, if needed, finiteness) and prove
them in that restricted setting.
-/

/-! ## Zone-Specific Safety Definitions -/

/-- Safety predicate for X925 performance cores. -/
def x925_safe (tempC : Float) : Prop :=
  SafeTemp ThermalBounds.x925Default tempC

/-- Safety predicate for A725 efficiency cores. -/
def a725_safe (tempC : Float) : Prop :=
  SafeTemp ThermalBounds.a725Default tempC

/-- Safety predicate for GPU. -/
def gpu_safe (tempC : Float) : Prop :=
  SafeTemp ThermalBounds.gpuDefault tempC

/-- Safety predicate for NVMe storage. -/
def nvme_safe (tempC : Float) : Prop :=
  SafeTemp ThermalBounds.nvmeDefault tempC

/-- Safety predicate for network adapters. -/
def network_safe (tempC : Float) : Prop :=
  SafeTemp ThermalBounds.networkDefault tempC

/-- Safety predicate for SoC peripherals (L3 cache, memory controller, VRM, I/O). -/
def soc_safe (tempC : Float) : Prop :=
  SafeTemp ThermalBounds.socDefault tempC

/-! ## Decidability for Runtime Binding -/

/-- Check if a temperature is safe (decidable). -/
def isSafeTempDecide (bounds : ThermalBounds) (tempC : Float) : Bool :=
  tempC < bounds.criticalC

/-- Check if a sample is safe (decidable). -/
def isSafeSampleDecide (sample : ThermalSample) : Bool :=
  let bounds := ThermalBounds.forCoreClass sample.zone.coreClass
  isSafeTempDecide bounds sample.tempC

/-- Check if all samples in a reading are safe (decidable). -/
def isSafeReadingDecide (reading : ThermalReading) : Bool :=
  reading.samples.all isSafeSampleDecide

/-- Check if a thermal state is safe (decidable). -/
def isSafeStateDecide (s : ThermalState) : Bool :=
  s.zones.all (fun p => isSafeTempDecide ThermalBounds.x925Default p.2)

end Thermal
end MirandaDynamics
end HeytingLean
