import HeytingLean.MirandaDynamics.Thermal.HardwareLedger.Basic
import HeytingLean.MirandaDynamics.Thermal.HardwareLedger.MeasurementModel
import HeytingLean.MirandaDynamics.Thermal.SafetyPredicates

/-!
# DGX Spark (GB10) hardware ledger: component-spec intervals + safety templates

This module turns "device presence" information into *parameterized* specs:
- we fix what NVIDIA documents (e.g. component presence, typical power budgets),
- we leave what is not documented (e.g. effective thermal resistances) as explicit intervals,
  so theorems remain honest.

Proof strategy:
- Prove conditional bounds in `Rat` using the lemmas in `HardwareLedger.Basic`.
- Provide thin "SafetyPredicates-facing" helper lemmas that connect the *idea* of a bound
  to the existing `SafeTemp` predicate (which is Float-based at runtime).
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal
namespace HardwareLedger

open ClosedIntervalQ

def ambientOperatingC : ClosedIntervalQ :=
  { lo := 5, hi := 30, h_lo_hi := by decide }

def gpuPowerBudgetW : ClosedIntervalQ :=
  -- Public docs: up to 140W TDP for Blackwell GPU in DGX Spark.
  { lo := 0, hi := 140, h_lo_hi := by decide }

def totalSystemPowerW : ClosedIntervalQ :=
  -- Public docs: 240W power supply (treat as an upper bound for sustained).
  { lo := 0, hi := 240, h_lo_hi := by decide }

def criticalGpuC : Rat := 100
def criticalNvmeC : Rat := 85
def criticalNetworkC : Rat := 90

/-!
## Measurement-model constants (Phase 1)

These are the Lean-side constants corresponding to the telemetry measurement model ledger.

Current calibration target:
- `data/hardware/dgx_spark_telemetry_measurement_model_v1.json`

Note: The Lean file cannot (yet) parse the JSON ledger, so we mirror the currently used
effective bound here for the key safety transfer lemma.
-/

def gpuTempAbsErrC : AbsErrorBoundQ :=
  -- Effective absolute bound used at runtime (measurement-model v1):
  --   abs_error_bound + bias_abs_bound + quantization_step/2
  -- = 0.0 + 1.0 + 1.0/2 = 1.5 C
  AbsErrorBoundQ.mk' (3 / 2) (by
    -- 0 <= 3/2
    norm_num)

theorem gpu_true_lt_critical_of_measured
    {t m : Rat}
    (ht : (measInterval m gpuTempAbsErrC).mem t)
    (h_meas : m + gpuTempAbsErrC.eps < criticalGpuC) :
    t < criticalGpuC := by
  exact true_lt_crit_of_mem_measInterval_and_hi_lt (t := t) (m := m) (crit := criticalGpuC)
    (e := gpuTempAbsErrC) ht h_meas

theorem gpu_steady_safe_if_hi_lt (rthCperW : ClosedIntervalQ)
    (hr_nonneg : 0 ≤ rthCperW.lo)
    (h_hi : steadyTempC ambientOperatingC.hi rthCperW.hi gpuPowerBudgetW.hi < criticalGpuC) :
    ∀ (rv : Rat), rthCperW.mem rv →
      ∀ (pw : Rat), gpuPowerBudgetW.mem pw →
        steadyTempC ambientOperatingC.hi rv pw < criticalGpuC := by
  -- A specialization of the general interval-safe template.
  have hp_nonneg : 0 ≤ gpuPowerBudgetW.lo := by decide
  simpa [ambientOperatingC, gpuPowerBudgetW, criticalGpuC] using
    (steadyTemp_safe_of_hi_lt (ambient := ambientOperatingC.hi) (crit := criticalGpuC)
      (r := rthCperW) (p := gpuPowerBudgetW)
      (hr_nonneg := hr_nonneg) (hp_nonneg := hp_nonneg) (h_hi := h_hi))

/-! ## Thin SafetyPredicates-facing helpers -/

theorem gpu_safe_of_lt_critical (tempC : Float) (h : tempC < ThermalBounds.gpuDefault.criticalC) :
    gpu_safe tempC := by
  -- definitional
  simpa [gpu_safe, SafeTemp] using h

theorem nvme_safe_of_lt_critical (tempC : Float) (h : tempC < ThermalBounds.nvmeDefault.criticalC) :
    nvme_safe tempC := by
  simpa [nvme_safe, SafeTemp] using h

theorem network_safe_of_lt_critical (tempC : Float) (h : tempC < ThermalBounds.networkDefault.criticalC) :
    network_safe tempC := by
  simpa [network_safe, SafeTemp] using h

end HardwareLedger
end Thermal
end MirandaDynamics
end HeytingLean
