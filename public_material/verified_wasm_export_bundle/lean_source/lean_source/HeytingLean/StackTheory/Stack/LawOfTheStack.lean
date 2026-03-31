import HeytingLean.StackTheory.Stack.MLA

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §5, Theorem 5.1: the next-layer utility is bounded by the previous layer's
extension width. The proof uses the ESM counting lemmas and the abstractor bound. -/
theorem law_of_the_stack (S : Stack Φ n) (i : Fin n)
    (hNonempty : (correctPolicies (S.vocab i.succ)
      (S.instantiatedTask i.succ)).Nonempty) :
    utility (S.vocab i.succ) (S.instantiatedTask i.succ) hNonempty
      + (S.instantiatedTask i.succ).outputs.card
      ≤ 2 ^ (extension (S.vocab i.castSucc) (S.policy i.castSucc)).card := by
  have hUtility :
      utility (S.vocab i.succ) (S.instantiatedTask i.succ) hNonempty
        + (S.instantiatedTask i.succ).outputs.card
        ≤ (language (S.vocab i.succ)).card :=
    utility_le_language (S.vocab i.succ) (S.instantiatedTask i.succ) hNonempty
  have hLanguage :
      (language (S.vocab i.succ)).card ≤ 2 ^ (S.vocab i.succ).card :=
    language_card_le_pow (S.vocab i.succ)
  -- `ext_subset_language` records Bennett's `Ext(πᵢ) ⊆ L_{vᵢ}` side of the four-lemma chain.
  have hVocabCard :
      (S.vocab i.succ).card ≤ (extension (S.vocab i.castSucc) (S.policy i.castSucc)).card := by
    simpa [S.vocab_step i] using
      (abstractor_card_le_ext (S.vocab i.castSucc) (S.policy i.castSucc))
  calc
    utility (S.vocab i.succ) (S.instantiatedTask i.succ) hNonempty
        + (S.instantiatedTask i.succ).outputs.card
      ≤ (language (S.vocab i.succ)).card := hUtility
    _ ≤ 2 ^ (S.vocab i.succ).card := hLanguage
    _ ≤ 2 ^ (extension (S.vocab i.castSucc) (S.policy i.castSucc)).card := by
          exact Nat.pow_le_pow_right (by decide) hVocabCard

end HeytingLean.StackTheory
