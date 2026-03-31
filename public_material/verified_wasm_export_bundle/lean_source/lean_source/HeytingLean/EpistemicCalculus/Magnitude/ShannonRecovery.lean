import HeytingLean.EpistemicCalculus.Magnitude.EnrichedMagnitude

namespace HeytingLean.EpistemicCalculus.Magnitude

open scoped BigOperators

/--
Historical module name aside, this file states only a conditional Tsallis-2
rewrite:
if magnitude is given by the diagonal-deficit shape, it rewrites as
`|Vocab| + Σ Tsallis₂`.
-/
theorem conditional_tsallis_bridge
    (Vocab : Type*) [Fintype Vocab] [DecidableEq Vocab]
    (Prompts : Type*) [Fintype Prompts]
    (nextToken : Prompts → Vocab → ℝ)
    (hnonneg : ∀ p v, 0 ≤ nextToken p v)
    (hnorm : ∀ p, Finset.sum Finset.univ (fun v => nextToken p v) = 1)
    (w : Prompts → ℝ)
    (hw : ∀ i, Finset.sum Finset.univ
      (fun j => (llmEnrichment Vocab Prompts nextToken hnonneg hnorm).sim i j * w j) = 1)
    (hmag :
      enrichedMagnitude (llmEnrichment Vocab Prompts nextToken hnonneg hnorm) w hw =
        (Fintype.card Vocab : ℝ) + (Fintype.card Prompts : ℝ) -
          Finset.sum Finset.univ
            (fun p => (llmEnrichment Vocab Prompts nextToken hnonneg hnorm).sim p p)) :
    enrichedMagnitude (llmEnrichment Vocab Prompts nextToken hnonneg hnorm) w hw =
      (Fintype.card Vocab : ℝ) +
        Finset.sum Finset.univ (fun p => tsallisEntropy 2 (nextToken p)) :=
  magnitude_eq_tsallis_sum_of_magnitude_shape
    Vocab Prompts nextToken hnonneg hnorm w hw hmag

end HeytingLean.EpistemicCalculus.Magnitude
