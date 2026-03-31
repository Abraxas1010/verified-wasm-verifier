import HeytingLean.StackTheory.Primitives.Environment

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §4: A statement is a finite sub-vocabulary. -/
structure Statement (v : Vocabulary Φ) where
  val : Finset (Program Φ)
  sub : val ⊆ v

/-- Bennett §4: The language `L_v` consists of statements with nonempty truth sets. -/
def language (v : Vocabulary Φ) : Finset (Finset (Program Φ)) :=
  v.powerset.filter (fun l => (truthSet l).Nonempty)

@[simp]
theorem mem_language {v : Vocabulary Φ} {l : Finset (Program Φ)} :
    l ∈ language v ↔ l ⊆ v ∧ (truthSet l).Nonempty := by
  simp [language]

/-- Bennett ESM Lemma 1: the language is bounded by the powerset of the vocabulary. -/
theorem language_card_le_pow (v : Vocabulary Φ) :
    (language v).card ≤ 2 ^ v.card := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_powerset v)

end HeytingLean.StackTheory
