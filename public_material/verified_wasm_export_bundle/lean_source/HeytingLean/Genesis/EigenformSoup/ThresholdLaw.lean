import Mathlib

/-!
# Genesis.EigenformSoup.ThresholdLaw

Threshold-law contracts used by LES-Omega:
depth `d` requires substrate size `N ≥ 2^(d+2)`.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Theoretical minimum substrate size for depth `d`: `2^(d+2)`. -/
def theoreticalMinSize (depth : Nat) : Nat :=
  Nat.shiftLeft 1 (depth + 2)

/-- Threshold satisfaction predicate for one `(size, depth)` pair. -/
def thresholdSatisfied (size depth : Nat) : Prop :=
  theoreticalMinSize depth ≤ size

/-- Falsification predicate: phase transition observed below theoretical minimum size. -/
def TheoreticalThresholdViolation
    (phaseTransitionDetected : Prop)
    (size depth : Nat) : Prop :=
  phaseTransitionDetected ∧ size < theoreticalMinSize depth

theorem no_violation_of_size_bound
    {phaseTransitionDetected : Prop}
    {size depth : Nat}
    (hsize : theoreticalMinSize depth ≤ size) :
    ¬ TheoreticalThresholdViolation phaseTransitionDetected size depth := by
  intro h
  rcases h with ⟨_, hlt⟩
  exact (Nat.not_lt.mpr hsize) hlt

theorem violation_implies_not_satisfied
    {phaseTransitionDetected : Prop}
    {size depth : Nat}
    (hviol : TheoreticalThresholdViolation phaseTransitionDetected size depth) :
    ¬ thresholdSatisfied size depth := by
  intro hs
  rcases hviol with ⟨_, hlt⟩
  exact (Nat.not_lt.mpr hs) hlt

theorem thresholdSatisfied_mono_size
    {size₁ size₂ depth : Nat}
    (hsize : size₁ ≤ size₂)
    (hsat : thresholdSatisfied size₁ depth) :
    thresholdSatisfied size₂ depth := by
  exact Nat.le_trans hsat hsize

end HeytingLean.Genesis.EigenformSoup

