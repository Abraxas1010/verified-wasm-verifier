import HeytingLean.Metrics.Magnitude.HomologyGroups
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HeytingLean
namespace Metrics
namespace Magnitude

open scoped BigOperators

/-- An enriched similarity space with `[0,1]`-valued kernel. -/
structure EnrichedSpace (α : Type*) [Fintype α] where
  sim : α → α → ℝ
  sim_nonneg : ∀ x y, 0 ≤ sim x y
  sim_le_one : ∀ x y, sim x y ≤ 1
  sim_symm : ∀ x y, sim x y = sim y x

/-- Tsallis `q`-entropy for finite real-valued weights. -/
noncomputable def tsallisEntropy {α : Type*} [Fintype α] (q : ℝ) (p : α → ℝ) : ℝ :=
  if q = 1 then
    -Finset.sum Finset.univ (fun x => p x * Real.log (p x))
  else
    (1 / (q - 1)) * (1 - Finset.sum Finset.univ (fun x => p x ^ q))

/-- Closed form of Tsallis entropy at `q = 2`. -/
theorem tsallisEntropy_two {α : Type*} [Fintype α] (p : α → ℝ) :
    tsallisEntropy 2 p = 1 - Finset.sum Finset.univ (fun x => p x ^ (2 : ℝ)) := by
  unfold tsallisEntropy
  have h2 : (2 : ℝ) ≠ 1 := by norm_num
  have hInv : ((2 : ℝ) - 1)⁻¹ = 1 := by norm_num
  simp [h2, hInv]

/-- LLM-style enrichment: similarity is the inner product of next-token distributions. -/
def llmEnrichment (Vocab : Type*) [Fintype Vocab] [DecidableEq Vocab]
    (Prompts : Type*) [Fintype Prompts]
    (nextToken : Prompts → Vocab → ℝ)
    (hnonneg : ∀ p v, 0 ≤ nextToken p v)
    (hnorm : ∀ p, Finset.sum Finset.univ (fun v => nextToken p v) = 1) :
    EnrichedSpace Prompts where
  sim := fun p₁ p₂ => Finset.sum Finset.univ (fun v => nextToken p₁ v * nextToken p₂ v)
  sim_nonneg := by
    intro p₁ p₂
    refine Finset.sum_nonneg ?_
    intro v hv
    exact mul_nonneg (hnonneg p₁ v) (hnonneg p₂ v)
  sim_le_one := by
    intro p₁ p₂
    have htoken_le_one : ∀ p v, nextToken p v ≤ 1 := by
      intro p v
      have hsingle : nextToken p v ≤ Finset.sum Finset.univ (fun u => nextToken p u) := by
        have hnn : ∀ u ∈ Finset.univ, 0 ≤ nextToken p u := by
          intro u hu
          exact hnonneg p u
        simpa using Finset.single_le_sum hnn (Finset.mem_univ v)
      simpa [hnorm p] using hsingle
    have hterm : ∀ v, nextToken p₁ v * nextToken p₂ v ≤ nextToken p₁ v := by
      intro v
      have h1 := hnonneg p₁ v
      have h2 := hnonneg p₂ v
      have h3 := htoken_le_one p₂ v
      nlinarith
    calc
      Finset.sum Finset.univ (fun v => nextToken p₁ v * nextToken p₂ v)
          ≤ Finset.sum Finset.univ (fun v => nextToken p₁ v) := by
            exact Finset.sum_le_sum (fun v hv => hterm v)
      _ = 1 := hnorm p₁
  sim_symm := by
    intro p₁ p₂
    refine Finset.sum_congr rfl ?_
    intro v hv
    ring

/-- Magnitude induced by a weighting witness. -/
def enrichedMagnitude {α : Type*} [Fintype α] (E : EnrichedSpace α) (w : α → ℝ)
    (_hw : ∀ i, Finset.sum Finset.univ (fun j => E.sim i j * w j) = 1) : ℝ :=
  Finset.sum Finset.univ w

/-- Diagonal similarity equals squared `L²` norm of the prompt distribution. -/
theorem llm_self_similarity_eq_squareSum
    (Vocab : Type*) [Fintype Vocab] [DecidableEq Vocab]
    (Prompts : Type*) [Fintype Prompts]
    (nextToken : Prompts → Vocab → ℝ)
    (hnonneg : ∀ p v, 0 ≤ nextToken p v)
    (hnorm : ∀ p, Finset.sum Finset.univ (fun v => nextToken p v) = 1)
    (p : Prompts) :
    (llmEnrichment Vocab Prompts nextToken hnonneg hnorm).sim p p =
      Finset.sum Finset.univ (fun v => (nextToken p v) ^ (2 : ℝ)) := by
  simp [llmEnrichment, pow_two]

/-- Prompt-wise Tsallis-2 sum as cardinality minus squared-mass sum. -/
theorem sum_tsallis_two_eq_card_prompts_sub_squareSum
    (Vocab : Type*) [Fintype Vocab] [DecidableEq Vocab]
    (Prompts : Type*) [Fintype Prompts]
    (nextToken : Prompts → Vocab → ℝ) :
    Finset.sum Finset.univ (fun p => tsallisEntropy 2 (nextToken p)) =
      (Fintype.card Prompts : ℝ) -
        Finset.sum Finset.univ
          (fun p => Finset.sum Finset.univ (fun v => (nextToken p v) ^ (2 : ℝ))) := by
  calc
    Finset.sum Finset.univ (fun p => tsallisEntropy 2 (nextToken p))
        = Finset.sum Finset.univ
            (fun p => (1 : ℝ) - Finset.sum Finset.univ (fun v => (nextToken p v) ^ (2 : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              simp [tsallisEntropy_two]
    _ = Finset.sum Finset.univ (fun _ : Prompts => (1 : ℝ)) -
          Finset.sum Finset.univ
            (fun p => Finset.sum Finset.univ (fun v => (nextToken p v) ^ (2 : ℝ))) := by
              simp [Finset.sum_sub_distrib]
    _ = (Fintype.card Prompts : ℝ) -
          Finset.sum Finset.univ
            (fun p => Finset.sum Finset.univ (fun v => (nextToken p v) ^ (2 : ℝ))) := by
              simp

/-- Non-discrete witness: if distinct prompts share positive token overlap, similarity is positive. -/
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
  rcases hpair with ⟨p₁, p₂, v, hneq, hv₁, hv₂⟩
  refine ⟨p₁, p₂, hneq, ?_⟩
  have htermNonneg : ∀ u, 0 ≤ nextToken p₁ u * nextToken p₂ u := by
    intro u
    exact mul_nonneg (hnonneg p₁ u) (hnonneg p₂ u)
  have hsingle :
      nextToken p₁ v * nextToken p₂ v ≤
        Finset.sum Finset.univ (fun u => nextToken p₁ u * nextToken p₂ u) := by
    have hnn : ∀ u ∈ Finset.univ, 0 ≤ nextToken p₁ u * nextToken p₂ u := by
      intro u hu
      exact htermNonneg u
    simpa using Finset.single_le_sum hnn (Finset.mem_univ v)
  have hposTerm : 0 < nextToken p₁ v * nextToken p₂ v := mul_pos hv₁ hv₂
  exact lt_of_lt_of_le hposTerm (by simpa [llmEnrichment] using hsingle)

/-- Conditional Tsallis bridge:
if magnitude has the card-vocab plus diagonal-deficit shape,
it rewrites to card-vocab plus Tsallis-2 sum. -/
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
  have hdiag :
      Finset.sum Finset.univ
        (fun p => (llmEnrichment Vocab Prompts nextToken hnonneg hnorm).sim p p) =
      Finset.sum Finset.univ
        (fun p => Finset.sum Finset.univ (fun v => (nextToken p v) ^ (2 : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact llm_self_similarity_eq_squareSum Vocab Prompts nextToken hnonneg hnorm p
  have hts :=
    sum_tsallis_two_eq_card_prompts_sub_squareSum Vocab Prompts nextToken
  calc
    enrichedMagnitude (llmEnrichment Vocab Prompts nextToken hnonneg hnorm) w hw
        = (Fintype.card Vocab : ℝ) + (Fintype.card Prompts : ℝ) -
            Finset.sum Finset.univ
              (fun p => (llmEnrichment Vocab Prompts nextToken hnonneg hnorm).sim p p) := hmag
    _ = (Fintype.card Vocab : ℝ) +
          ((Fintype.card Prompts : ℝ) -
            Finset.sum Finset.univ
              (fun p => Finset.sum Finset.univ (fun v => (nextToken p v) ^ (2 : ℝ)))) := by
          rw [hdiag]
          ring
    _ = (Fintype.card Vocab : ℝ) +
          Finset.sum Finset.univ (fun p => tsallisEntropy 2 (nextToken p)) := by
          rw [hts]

end Magnitude
end Metrics
end HeytingLean
