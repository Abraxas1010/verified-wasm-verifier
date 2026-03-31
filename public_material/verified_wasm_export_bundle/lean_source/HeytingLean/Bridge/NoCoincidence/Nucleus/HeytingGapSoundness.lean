import HeytingLean.Bridge.NoCoincidence.Nucleus.CircuitNucleus
import HeytingLean.HossenfelderNoGo.HeytingBoundary.GapNonZero

namespace HeytingLean.Bridge.NoCoincidence.Nucleus

open HeytingLean
open HeytingLean.HossenfelderNoGo.HeytingBoundary

/-- Property-level Heyting gap for the circuit nucleus: the closure says `P`, but `P` itself does
not. These are the algebraic false positives carried by the nucleus. -/
def circuitHeytingGap (R : CircuitNucleus n) (P : CircuitProp n) : Set (Basic.RevCircuit n) :=
  { C | (R.toNucleus.R P) C ∧ ¬ P C }

theorem mem_circuitHeytingGap_iff (R : CircuitNucleus n) (P : CircuitProp n) (C : Basic.RevCircuit n) :
    C ∈ circuitHeytingGap R P ↔ (R.toNucleus.R P) C ∧ ¬ P C := Iff.rfl

/-- The circuit nucleus is already a Hossenfelder boundary nucleus. -/
abbrev circuitBoundaryNucleus (R : CircuitNucleus n) :
    BoundaryNucleus (CircuitProp n) :=
  R.toNucleus

theorem circuit_boundary_non_boolean (R : CircuitNucleus n)
    (hBridge : BooleanBoundaryBridge (circuitBoundaryNucleus R)) :
    ¬ isBoolean (circuitBoundaryNucleus R) :=
  boundary_necessarily_non_boolean (circuitBoundaryNucleus R) hBridge

theorem circuit_boundary_gap_nonempty (R : CircuitNucleus n) (P : CircuitProp n)
    (hGap : ∃ C, C ∈ circuitHeytingGap R P) :
    boundaryGap (circuitBoundaryNucleus R) P ≠ ∅ := by
  obtain ⟨C, hC⟩ := hGap
  intro hEmpty
  have hEq : (circuitBoundaryNucleus R).R P = P := by
    by_contra hneq
    have hmem : (circuitBoundaryNucleus R).R P ∈ boundaryGap (circuitBoundaryNucleus R) P := by
      simp [boundaryGap, hneq]
    simp [hEmpty] at hmem
  exact hC.2 (by simpa [hEq] using hC.1)

theorem gap_characterizes_soundness (R : CircuitNucleus n) (P : CircuitProp n) :
    (∃ C, C ∈ circuitHeytingGap R P) ↔ boundaryGap (circuitBoundaryNucleus R) P ≠ ∅ := by
  constructor
  · intro hGap
    exact circuit_boundary_gap_nonempty R P hGap
  · intro hGap
    have hneq : (circuitBoundaryNucleus R).R P ≠ P := by
      intro hEq
      have : boundaryGap (circuitBoundaryNucleus R) P = ∅ := by
        ext Q
        simp [boundaryGap, hEq]
      exact hGap this
    have hfun : ∃ C, (R.toNucleus.R P) C ≠ P C := by
      classical
      exact not_forall.mp (by
        intro hAll
        apply hneq
        funext C
        exact propext ⟨fun h => by simpa [hAll C] using h, fun h => by simpa [hAll C] using h⟩)
    rcases hfun with ⟨C, hC⟩
    have hTrue : (R.toNucleus.R P) C := by
      by_cases hPC : P C
      · have : P C := hPC
        have hRPC : (R.toNucleus.R P) C := R.toNucleus.extensive P C this
        exact False.elim (hC (by simp [hPC, hRPC]))
      · by_cases hRPC : (R.toNucleus.R P) C
        · exact hRPC
        · exact False.elim (hC (by simp [hPC, hRPC]))
    have hFalse : ¬ P C := by
      by_contra hPC
      have hRPC : (R.toNucleus.R P) C := R.toNucleus.extensive P C hPC
      exact hC (by simp [hPC, hRPC])
    exact ⟨C, ⟨hTrue, hFalse⟩⟩

end HeytingLean.Bridge.NoCoincidence.Nucleus
