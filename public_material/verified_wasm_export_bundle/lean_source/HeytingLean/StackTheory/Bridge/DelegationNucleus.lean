import HeytingLean.Core.Nucleus
import HeytingLean.StackTheory.Stack.MLA

namespace HeytingLean.StackTheory.Bridge

open HeytingLean

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett bridge novelty: push the abstractor through a nucleus on truth sets. -/
def abstractorThroughNucleus
    (N : Core.Nucleus (Finset Φ))
    (v : HeytingLean.StackTheory.Vocabulary Φ)
    (π : Finset (HeytingLean.StackTheory.Program Φ)) :
    HeytingLean.StackTheory.Vocabulary Φ :=
  (HeytingLean.StackTheory.extension v π).image
    (fun o => N.R (HeytingLean.StackTheory.truthSet o))

/-- Bennett bridge novelty: the nucleus-mediated abstractor is still bounded by the
extension width. -/
theorem abstractorThroughNucleus_card_le_extension
    (N : Core.Nucleus (Finset Φ))
    (v : HeytingLean.StackTheory.Vocabulary Φ)
    (π : Finset (HeytingLean.StackTheory.Program Φ)) :
    (abstractorThroughNucleus N v π).card ≤
      (HeytingLean.StackTheory.extension v π).card := by
  exact Finset.card_image_le

/-- Bennett bridge novelty: if every abstracted truth set is already nucleus-fixed, the
nucleus-mediated abstractor collapses back to Bennett's ordinary abstractor. -/
theorem abstractorThroughNucleus_eq_abstractor_of_fixed
    (N : Core.Nucleus (Finset Φ))
    (v : HeytingLean.StackTheory.Vocabulary Φ)
    (π : Finset (HeytingLean.StackTheory.Program Φ))
    (hFixed :
      ∀ o ∈ HeytingLean.StackTheory.extension v π,
        N.R (HeytingLean.StackTheory.truthSet o) =
          HeytingLean.StackTheory.truthSet o) :
    abstractorThroughNucleus N v π =
      HeytingLean.StackTheory.abstractor v π := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨o, ho, hs⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨o, ho, ?_⟩
    rw [hFixed o ho] at hs
    exact hs
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨o, ho, hs⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨o, ho, ?_⟩
    rw [hFixed o ho, hs]

end HeytingLean.StackTheory.Bridge
