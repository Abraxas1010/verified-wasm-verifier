import HeytingLean.MirandaDynamics.Thermal.HardwareLedger.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

/-!
# Thermal Hardware Ledger: Measurement Model

This module provides a *proof-friendly* interface for turning raw telemetry
into interval claims under an explicit measurement-error assumption.

Key idea:
- We do not "prove hardware behavior".
- We prove *conditional* statements: if true values lie within declared error bounds,
  then safety/interval conclusions follow.

This is the Lean counterpart of the JSON "telemetry measurement model" ledger.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal
namespace HardwareLedger

/-- Absolute error bound (in the same unit as the measured quantity). -/
structure AbsErrorBoundQ where
  eps : Rat
  h_nonneg : 0 ≤ eps
  deriving Repr

namespace AbsErrorBoundQ

def mk' (eps : Rat) (h : 0 ≤ eps) : AbsErrorBoundQ := { eps := eps, h_nonneg := h }

end AbsErrorBoundQ

/-- Interval of possible true values for a measurement `m` under an absolute error bound. -/
def measInterval (m : Rat) (e : AbsErrorBoundQ) : ClosedIntervalQ :=
  { lo := m - e.eps
    hi := m + e.eps
    h_lo_hi := by
      have : 0 ≤ e.eps := e.h_nonneg
      linarith }

theorem true_le_hi_of_mem_measInterval {t m : Rat} {e : AbsErrorBoundQ}
    (ht : (measInterval m e).mem t) : t ≤ m + e.eps := by
  -- `mem` is `(lo ≤ t) ∧ (t ≤ hi)`.
  exact ht.2

/-- Safety transfer: if the measurement interval's upper endpoint is below `crit`,
then any true value inside the interval is below `crit`. -/
theorem true_lt_crit_of_mem_measInterval_and_hi_lt
    {t m crit : Rat} {e : AbsErrorBoundQ}
    (ht : (measInterval m e).mem t)
    (h_hi : m + e.eps < crit) :
    t < crit := by
  have hle : t ≤ m + e.eps := true_le_hi_of_mem_measInterval (t := t) (m := m) (e := e) ht
  exact lt_of_le_of_lt hle h_hi

/-- Interval for a difference `t1 - t0` given two measurements `m0,m1` and error bounds. -/
def deltaInterval (m0 m1 : Rat) (e0 e1 : AbsErrorBoundQ) : ClosedIntervalQ :=
  let eSum : Rat := e0.eps + e1.eps
  have hnonneg : 0 ≤ eSum := by linarith [e0.h_nonneg, e1.h_nonneg]
  { lo := (m1 - m0) - eSum
    hi := (m1 - m0) + eSum
    h_lo_hi := by
      -- (x - e) ≤ (x + e) when e ≥ 0
      linarith [hnonneg] }

/-- If true temperatures lie within their measurement intervals, then the true delta lies within
`deltaInterval`. This is the basic bridge used to bound dT and rate-like quantities. -/
theorem delta_mem_of_mem_measIntervals
    {t0 t1 m0 m1 : Rat} {e0 e1 : AbsErrorBoundQ}
    (h0 : (measInterval m0 e0).mem t0)
    (h1 : (measInterval m1 e1).mem t1) :
    (deltaInterval m0 m1 e0 e1).mem (t1 - t0) := by
  -- Unpack bounds.
  have ht0_lo : m0 - e0.eps ≤ t0 := h0.1
  have ht0_hi : t0 ≤ m0 + e0.eps := h0.2
  have ht1_lo : m1 - e1.eps ≤ t1 := h1.1
  have ht1_hi : t1 ≤ m1 + e1.eps := h1.2

  -- Lower bound: (m1 - e1) - (m0 + e0) ≤ t1 - t0
  have h_lo : (m1 - m0) - (e0.eps + e1.eps) ≤ (t1 - t0) := by
    linarith
  -- Upper bound: t1 - t0 ≤ (m1 + e1) - (m0 - e0)
  have h_hi : (t1 - t0) ≤ (m1 - m0) + (e0.eps + e1.eps) := by
    linarith

  unfold deltaInterval
  -- `deltaInterval` is defined via `let`; `simp` unfolds it.
  simp [ClosedIntervalQ.mem, h_lo, h_hi]

end HardwareLedger
end Thermal
end MirandaDynamics
end HeytingLean

