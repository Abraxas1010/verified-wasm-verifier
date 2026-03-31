import HeytingLean.Metrics.Magnitude.EnrichedMagnitude

namespace HeytingLean.EpistemicCalculus.Magnitude

open scoped BigOperators

/-- Tsallis entropy on finite real-valued weights. -/
noncomputable abbrev tsallisEntropy {α : Type*} [Fintype α] (q : ℝ) (p : α → ℝ) : ℝ :=
  HeytingLean.Metrics.Magnitude.tsallisEntropy q p

theorem tsallis_two_eq {α : Type*} [Fintype α] (p : α → ℝ) :
    tsallisEntropy 2 p = 1 - Finset.sum Finset.univ (fun i => (p i) ^ (2 : ℝ)) := by
  simpa [tsallisEntropy] using HeytingLean.Metrics.Magnitude.tsallisEntropy_two p

theorem tsallis_one_eq_negSum {α : Type*} [Fintype α] (p : α → ℝ) :
    tsallisEntropy 1 p = -Finset.sum Finset.univ (fun i => p i * Real.log (p i)) := by
  unfold tsallisEntropy HeytingLean.Metrics.Magnitude.tsallisEntropy
  simp

end HeytingLean.EpistemicCalculus.Magnitude
