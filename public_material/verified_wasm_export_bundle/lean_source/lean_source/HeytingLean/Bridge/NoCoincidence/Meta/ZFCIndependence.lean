import HeytingLean.Bridge.NoCoincidence.Nucleus.HeytingGapSoundness

namespace HeytingLean.Bridge.NoCoincidence.Meta

open HeytingLean.Bridge.NoCoincidence.Nucleus
open HeytingLean.HossenfelderNoGo.HeytingBoundary

/-- Boolean collapse kills the circuit Heyting gap. This is the formal structural reason that the
CNCC sits more naturally in a Heyting setting than in a Boolean one. -/
theorem zfc_independence_heuristic (R : CircuitNucleus n) (P : CircuitProp n)
    (hBool : isBoolean (circuitBoundaryNucleus R)) :
    circuitHeytingGap R P = ∅ := by
  ext C
  constructor
  · intro hGap
    have hEq : (circuitBoundaryNucleus R).R P = P := hBool P
    exact False.elim (hGap.2 (by simpa [hEq] using hGap.1))
  · intro hFalse
    simp at hFalse

end HeytingLean.Bridge.NoCoincidence.Meta
