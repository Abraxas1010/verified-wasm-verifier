import HeytingLean.StackTheory.Primitives.Language

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §4: `l'` is a completion of `l` when it lies in the language and extends `l`. -/
def isCompletion (v : Vocabulary Φ) (l l' : Finset (Program Φ)) : Prop :=
  l' ∈ language v ∧ l ⊆ l'

/-- Bennett §4: The extension of a policy is the set of its completions. -/
def extension (v : Vocabulary Φ) (l : Finset (Program Φ)) : Finset (Finset (Program Φ)) :=
  (language v).filter (fun l' => l ⊆ l')

/-- Bennett §4: Weakness is the cardinality of the extension set. -/
def weakness (v : Vocabulary Φ) (π : Finset (Program Φ)) : ℕ :=
  (extension v π).card

@[simp]
theorem mem_extension {v : Vocabulary Φ} {l l' : Finset (Program Φ)} :
    l' ∈ extension v l ↔ l' ∈ language v ∧ l ⊆ l' := by
  simp [extension, and_assoc]

/-- Bennett ESM Lemma 2: every completion lies in the ambient language. -/
theorem ext_subset_language (v : Vocabulary Φ) (π : Finset (Program Φ)) :
    extension v π ⊆ language v := by
  exact Finset.filter_subset _ _

/-- Bennett §4: weaker policies have larger extensions. -/
theorem ext_mono (v : Vocabulary Φ) (π π' : Finset (Program Φ))
    (h : π ⊆ π') :
    extension v π' ⊆ extension v π := by
  intro l hl
  rcases (mem_extension.mp hl) with ⟨hlang, hsub⟩
  exact mem_extension.mpr ⟨hlang, h.trans hsub⟩

/-- Bennett §4: every extension is bounded by the ambient language. -/
theorem weakness_le_language (v : Vocabulary Φ) (π : Finset (Program Φ)) :
    weakness v π ≤ (language v).card := by
  exact Finset.card_le_card (ext_subset_language v π)

end HeytingLean.StackTheory
