import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Thermal Hardware Ledger (Basic)

This folder provides an assumption-aware, proof-friendly core for reasoning about
"likely hardware materials" and simple thermal/power safety bounds.

We work over `Rat` (rational numbers) for stability and to avoid IEEE `Float` issues
(NaN, non-total order). Runtime telemetry is still `Float`, but the *proof layer*
is best expressed over exact arithmetic and interval bounds.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal
namespace HardwareLedger

structure ClosedIntervalQ where
  lo : Rat
  hi : Rat
  h_lo_hi : lo ≤ hi
  deriving Repr

namespace ClosedIntervalQ

def mem (i : ClosedIntervalQ) (x : Rat) : Prop :=
  i.lo ≤ x ∧ x ≤ i.hi

theorem mem_lo (i : ClosedIntervalQ) : mem i i.lo := by
  unfold mem
  constructor
  · exact le_rfl
  · exact i.h_lo_hi

theorem mem_hi (i : ClosedIntervalQ) : mem i i.hi := by
  unfold mem
  constructor
  · exact i.h_lo_hi
  · exact le_rfl

end ClosedIntervalQ

/-- Steady-state temperature model (very small "Newton cooling" abstraction):
`T = T_ambient + R_th * P`.

This is a *bounding* model. Real systems are dynamic and spatially nonuniform; in Phase 1
we use this only as a conservative proof template tied to intervals.
-/
def steadyTempC (ambientC rth_C_per_W powerW : Rat) : Rat :=
  ambientC + rth_C_per_W * powerW

theorem steadyTemp_mono_power {a r p1 p2 : Rat} (hr : 0 ≤ r) (hp : p1 ≤ p2) :
    steadyTempC a r p1 ≤ steadyTempC a r p2 := by
  unfold steadyTempC
  nlinarith

theorem steadyTemp_mono_rth {a r1 r2 p : Rat} (hp : 0 ≤ p) (hr : r1 ≤ r2) :
    steadyTempC a r1 p ≤ steadyTempC a r2 p := by
  unfold steadyTempC
  nlinarith

/-- A component-level sufficient condition for steady-state safety:
if `ambient + r_hi * p_hi < crit` then for any `r ∈ [r_lo,r_hi]` and `p ∈ [p_lo,p_hi]`,
we have `steadyTempC ambient r p < crit`.
-/
theorem steadyTemp_safe_of_hi_lt
    {ambient crit : Rat} {r p : ClosedIntervalQ}
    (hr_nonneg : 0 ≤ r.lo)
    (hp_nonneg : 0 ≤ p.lo)
    (h_hi : steadyTempC ambient r.hi p.hi < crit) :
    ∀ (rv : Rat), r.mem rv → ∀ (pv : Rat), p.mem pv → steadyTempC ambient rv pv < crit := by
  intro rv hrv pv hpv
  have hr1 : r.lo ≤ rv := hrv.1
  have hr2 : rv ≤ r.hi := hrv.2
  have hp1 : p.lo ≤ pv := hpv.1
  have hp2 : pv ≤ p.hi := hpv.2
  have hrv_nonneg : 0 ≤ rv := le_trans hr_nonneg hr1
  have hpv_nonneg : 0 ≤ pv := le_trans hp_nonneg hp1
  have hA : steadyTempC ambient rv pv ≤ steadyTempC ambient r.hi pv := by
    -- monotone in r for p >= 0
    have : rv ≤ r.hi := hr2
    have := steadyTemp_mono_rth (a := ambient) (p := pv) (hp := hpv_nonneg) this
    exact this
  have hB : steadyTempC ambient r.hi pv ≤ steadyTempC ambient r.hi p.hi := by
    -- monotone in p for r >= 0 (use r.hi >= r.lo >= 0)
    have rh_hi_nonneg : 0 ≤ r.hi := le_trans hr_nonneg r.h_lo_hi
    have : pv ≤ p.hi := hp2
    have := steadyTemp_mono_power (a := ambient) (r := r.hi) (p1 := pv) (p2 := p.hi) rh_hi_nonneg this
    exact this
  have h_le : steadyTempC ambient rv pv ≤ steadyTempC ambient r.hi p.hi := le_trans hA hB
  exact lt_of_le_of_lt h_le h_hi

end HardwareLedger
end Thermal
end MirandaDynamics
end HeytingLean
