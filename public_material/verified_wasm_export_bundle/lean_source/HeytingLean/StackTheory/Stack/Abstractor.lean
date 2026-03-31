import HeytingLean.StackTheory.Primitives.Task

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §5: The abstractor sends a policy to the truth sets of its completions. -/
def abstractor (v : Vocabulary Φ) (π : Finset (Program Φ)) : Vocabulary Φ :=
  (extension v π).image truthSet

/-- Bennett ESM Lemma 4: the abstractor image is bounded by the extension width. -/
theorem abstractor_card_le_ext (v : Vocabulary Φ) (π : Finset (Program Φ)) :
    (abstractor v π).card ≤ (extension v π).card := by
  exact Finset.card_image_le

/-- Bennett §5: An uninstantiated task assigns a concrete task to each vocabulary. -/
abbrev UninstantiatedTask (Φ : Type*) [DecidableEq Φ] [Fintype Φ] :=
  (v : Vocabulary Φ) → VTask v

end HeytingLean.StackTheory
