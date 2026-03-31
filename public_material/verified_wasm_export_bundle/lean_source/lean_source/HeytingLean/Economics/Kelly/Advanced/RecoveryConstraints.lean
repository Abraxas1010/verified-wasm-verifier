import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import HeytingLean.Economics.Kelly.Core

namespace HeytingLean
namespace Economics
namespace Kelly
namespace Advanced

noncomputable section

open scoped BigOperators

open MeasureTheory

variable {Ω : Type*}

/-- “Recover within T steps”: the wealth process crosses back above `α` at some time `n ≤ T`. -/
def recoversWithin (W0 f : ℝ) (R : ℕ → Ω → ℝ) (α : ℝ) (T : ℕ) (ω : Ω) : Prop :=
  ∃ n ≤ T, wealthR (Ω := Ω) W0 f R n ω ≥ α

/-- A simple probabilistic recovery constraint (in `ℝ≥0∞`): the recovery event has probability at
least `1 - δ`. -/
def satisfiesRecoveryConstraint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W0 f : ℝ) (R : ℕ → Ω → ℝ) (α : ℝ) (T : ℕ) (δ : ENNReal) : Prop :=
  μ {ω | recoversWithin (Ω := Ω) W0 f R α T ω} ≥ 1 - δ

theorem recoversWithin_of_le_W0 (W0 f : ℝ) (R : ℕ → Ω → ℝ) (α : ℝ) (T : ℕ)
    (hα : α ≤ W0) : ∀ ω, recoversWithin (Ω := Ω) W0 f R α T ω := by
  intro ω
  refine ⟨0, ?_, ?_⟩
  · exact Nat.zero_le T
  · simpa [recoversWithin, wealthR_zero] using hα

theorem satisfiesRecoveryConstraint_of_le_W0
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W0 f : ℝ) (R : ℕ → Ω → ℝ) (α : ℝ) (T : ℕ) (δ : ENNReal)
    (hα : α ≤ W0) :
    satisfiesRecoveryConstraint (Ω := Ω) μ W0 f R α T δ := by
  have hall : ∀ ω, recoversWithin (Ω := Ω) W0 f R α T ω :=
    recoversWithin_of_le_W0 (Ω := Ω) (W0 := W0) (f := f) (R := R) (α := α) (T := T) hα
  have hset : {ω | recoversWithin (Ω := Ω) W0 f R α T ω} = Set.univ := by
    ext ω
    simp [hall ω]
  -- If the event holds for all outcomes, its probability is `1`, hence ≥ `1 - δ`.
  have hμ : μ {ω | recoversWithin (Ω := Ω) W0 f R α T ω} = 1 := by
    simp [hset]
  -- Rewrite the goal with `hμ`.
  simp [satisfiesRecoveryConstraint, hμ, ge_iff_le]

end

end Advanced
end Kelly
end Economics
end HeytingLean
