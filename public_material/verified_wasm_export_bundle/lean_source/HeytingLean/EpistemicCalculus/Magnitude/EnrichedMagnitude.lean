import HeytingLean.EpistemicCalculus.Magnitude.TsallisEntropy
import HeytingLean.Metrics.Magnitude.EnrichedMagnitude

namespace HeytingLean.EpistemicCalculus.Magnitude

open scoped BigOperators

/-- Re-export of the shared enriched-kernel structure from `Metrics.Magnitude`. -/
abbrev EnrichedSpace (α : Type*) [Fintype α] :=
  HeytingLean.Metrics.Magnitude.EnrichedSpace α

/--
LLM-style enrichment: similarity is the inner product of next-token
distributions.
-/
abbrev llmEnrichment (Vocab : Type*) [Fintype Vocab] [DecidableEq Vocab]
    (Prompts : Type*) [Fintype Prompts]
    (nextToken : Prompts → Vocab → ℝ)
    (hnonneg : ∀ p v, 0 ≤ nextToken p v)
    (hnorm : ∀ p, Finset.sum Finset.univ (fun v => nextToken p v) = 1) :=
  HeytingLean.Metrics.Magnitude.llmEnrichment
    Vocab Prompts nextToken hnonneg hnorm

/-- Magnitude extracted from a weighting witness `sim * w = 1`. -/
abbrev enrichedMagnitude {α : Type*} [Fintype α] (E : EnrichedSpace α) (w : α → ℝ)
    (hw : ∀ i, Finset.sum Finset.univ (fun j => E.sim i j * w j) = 1) : ℝ :=
  HeytingLean.Metrics.Magnitude.enrichedMagnitude E w hw

theorem llm_self_similarity_eq_squareSum
    (Vocab : Type*) [Fintype Vocab] [DecidableEq Vocab]
    (Prompts : Type*) [Fintype Prompts]
    (nextToken : Prompts → Vocab → ℝ)
    (hnonneg : ∀ p v, 0 ≤ nextToken p v)
    (hnorm : ∀ p, Finset.sum Finset.univ (fun v => nextToken p v) = 1)
    (p : Prompts) :
    (llmEnrichment Vocab Prompts nextToken hnonneg hnorm).sim p p =
      Finset.sum Finset.univ (fun v => (nextToken p v) ^ (2 : ℝ)) := by
  simpa [llmEnrichment] using
    HeytingLean.Metrics.Magnitude.llm_self_similarity_eq_squareSum
      Vocab Prompts nextToken hnonneg hnorm p

theorem sum_tsallis_two_eq_card_prompts_sub_squareSum
    (Vocab : Type*) [Fintype Vocab] [DecidableEq Vocab]
    (Prompts : Type*) [Fintype Prompts]
    (nextToken : Prompts → Vocab → ℝ) :
    Finset.sum Finset.univ (fun p => tsallisEntropy 2 (nextToken p)) =
      (Fintype.card Prompts : ℝ) -
        Finset.sum Finset.univ
          (fun p => Finset.sum Finset.univ (fun v => (nextToken p v) ^ (2 : ℝ))) := by
  simpa [tsallisEntropy] using
    HeytingLean.Metrics.Magnitude.sum_tsallis_two_eq_card_prompts_sub_squareSum
      Vocab Prompts nextToken

theorem llm_similarity_pos_for_distinct_with_overlap
    (Vocab : Type*) [Fintype Vocab] [DecidableEq Vocab]
    (Prompts : Type*) [Fintype Prompts]
    (nextToken : Prompts → Vocab → ℝ)
    (hnonneg : ∀ p v, 0 ≤ nextToken p v)
    (hnorm : ∀ p, Finset.sum Finset.univ (fun v => nextToken p v) = 1)
    (hpair : ∃ p₁ p₂ v,
      p₁ ≠ p₂ ∧ 0 < nextToken p₁ v ∧ 0 < nextToken p₂ v) :
    ∃ p₁ p₂, p₁ ≠ p₂ ∧
      0 < (llmEnrichment Vocab Prompts nextToken hnonneg hnorm).sim p₁ p₂ := by
  simpa [llmEnrichment] using
    HeytingLean.Metrics.Magnitude.llm_similarity_pos_for_distinct_with_overlap
      Vocab Prompts nextToken hnonneg hnorm hpair

/--
Conditional Tsallis bridge:
if magnitude has the card-vocab plus diagonal-deficit shape, it rewrites to
card-vocab plus Tsallis-2 sum.
-/
theorem magnitude_eq_tsallis_sum_of_magnitude_shape
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
        Finset.sum Finset.univ (fun p => tsallisEntropy 2 (nextToken p)) := by
  simpa [llmEnrichment, enrichedMagnitude, tsallisEntropy] using
    HeytingLean.Metrics.Magnitude.magnitude_eq_tsallis_sum_of_magnitude_shape
      Vocab Prompts nextToken hnonneg hnorm w hw hmag

end HeytingLean.EpistemicCalculus.Magnitude
