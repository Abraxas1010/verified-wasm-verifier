import Mathlib
import HeytingLean.Analysis.PMBoundedControl.TauProgression

/-!
# Soft Transition Gate
-/

namespace HeytingLean
namespace Analysis
namespace PMBoundedControl

noncomputable section

/-- Clamp a real number to the unit interval. -/
def clamp01 (x : ℝ) : ℝ :=
  max 0 (min 1 x)

/-- Monotone gate weight for blending between classical and completed updates. -/
def gateWeight (Q Q_PM ε : ℝ) : ℝ :=
  clamp01 ((Q - (Q_PM - ε)) / ε)

/-- Convex blend between a classical and PM-completed update. -/
def blendedUpdate (ω classical completed : ℝ) : ℝ :=
  (1 - ω) * classical + ω * completed

theorem clamp01_mem_unit_interval (x : ℝ) :
    0 ≤ clamp01 x ∧ clamp01 x ≤ 1 := by
  unfold clamp01
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem gate_in_unit_interval (Q Q_PM ε : ℝ) :
    0 ≤ gateWeight Q Q_PM ε ∧ gateWeight Q Q_PM ε ≤ 1 := by
  unfold gateWeight
  exact clamp01_mem_unit_interval _

theorem blended_bounded {ω classical completed B : ℝ}
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hclassical : |classical| ≤ B) (hcompleted : |completed| ≤ B) :
    |blendedUpdate ω classical completed| ≤ B := by
  unfold blendedUpdate
  have h1 : |(1 - ω) * classical| ≤ (1 - ω) * B := by
    rw [abs_mul]
    have hω : 0 ≤ 1 - ω := by linarith
    rw [abs_of_nonneg hω]
    gcongr
  have h2 : |ω * completed| ≤ ω * B := by
    rw [abs_mul, abs_of_nonneg hω0]
    gcongr
  calc
    |(1 - ω) * classical + ω * completed|
        ≤ |(1 - ω) * classical| + |ω * completed| := by
          simpa using norm_add_le ((1 - ω) * classical) (ω * completed)
    _ ≤ (1 - ω) * B + ω * B := by linarith
    _ = B := by ring

theorem blended_classical_when_safe {Q Q_PM ε classical completed : ℝ}
    (hε : 0 < ε) (hQ : Q ≤ Q_PM - ε) :
    blendedUpdate (gateWeight Q Q_PM ε) classical completed = classical := by
  unfold blendedUpdate gateWeight clamp01
  have hratio : (Q - (Q_PM - ε)) / ε ≤ 0 := by
    have hnum : Q - (Q_PM - ε) ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum hε.le
  have hmin : min 1 ((Q - (Q_PM - ε)) / ε) ≤ 0 := by
    exact le_trans (min_le_right _ _) hratio
  have hclamp : max 0 (min 1 ((Q - (Q_PM - ε)) / ε)) = 0 := by
    exact max_eq_left hmin
  simp [hclamp]

theorem blended_completed_when_critical {Q Q_PM ε classical completed : ℝ}
    (hε : 0 < ε) (hQ : Q_PM ≤ Q) :
    blendedUpdate (gateWeight Q Q_PM ε) classical completed = completed := by
  unfold blendedUpdate gateWeight clamp01
  have hratio : 1 ≤ (Q - (Q_PM - ε)) / ε := by
    have hnum : ε ≤ Q - (Q_PM - ε) := by linarith
    exact (one_le_div hε).2 hnum
  have hmin : min 1 ((Q - (Q_PM - ε)) / ε) = 1 := min_eq_left hratio
  simp [hmin]

end

end PMBoundedControl
end Analysis
end HeytingLean
