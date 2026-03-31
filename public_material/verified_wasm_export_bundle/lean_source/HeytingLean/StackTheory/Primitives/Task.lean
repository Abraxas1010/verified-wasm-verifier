import Mathlib.Data.Finset.Max
import HeytingLean.StackTheory.Primitives.Extension

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §4: A `v`-task is specified by admissible inputs and correct outputs. -/
structure VTask (v : Vocabulary Φ) where
  inputs : Finset (Finset (Program Φ))
  outputs : Finset (Finset (Program Φ))
  outputs_sub : outputs ⊆ inputs.biUnion (extension v)

/-- Bennett §4: Correct policies are those whose completions agree with the task outputs
on the admissible inputs. -/
def correctPolicies (v : Vocabulary Φ) (α : VTask v) : Finset (Finset (Program Φ)) :=
  (language v).filter (fun π =>
    ((α.inputs.biUnion (extension v)) ∩ extension v π) = α.outputs)

@[simp]
theorem mem_correctPolicies {v : Vocabulary Φ} {α : VTask v} {π : Finset (Program Φ)} :
    π ∈ correctPolicies v α ↔
      π ∈ language v ∧ ((α.inputs.biUnion (extension v)) ∩ extension v π) = α.outputs := by
  simp [correctPolicies]

/-- Bennett §4: Utility is the best extension width minus the task's output width. -/
noncomputable def utility (v : Vocabulary Φ) (α : VTask v)
    (h : (correctPolicies v α).Nonempty) : ℕ :=
  (correctPolicies v α).sup' h (fun π => weakness v π) - α.outputs.card

/-- Bennett §4: Every correct policy contains the task outputs inside its extension set. -/
theorem outputs_subset_extension_of_mem_correctPolicies
    {v : Vocabulary Φ} {α : VTask v} {π : Finset (Program Φ)}
    (hπ : π ∈ correctPolicies v α) :
    α.outputs ⊆ extension v π := by
  intro o ho
  have hEq : ((α.inputs.biUnion (extension v)) ∩ extension v π) = α.outputs :=
    (mem_correctPolicies.mp hπ).2
  have ho' : o ∈ (α.inputs.biUnion (extension v)) ∩ extension v π := by
    simpa [hEq] using ho
  exact (Finset.mem_inter.mp ho').2

/-- Bennett §4: The task outputs are bounded by the weakness of any correct policy. -/
theorem outputs_card_le_weakness_of_mem_correctPolicies
    {v : Vocabulary Φ} {α : VTask v} {π : Finset (Program Φ)}
    (hπ : π ∈ correctPolicies v α) :
    α.outputs.card ≤ weakness v π := by
  exact Finset.card_le_card (outputs_subset_extension_of_mem_correctPolicies hπ)

/-- Bennett ESM Lemma 3: utility plus realized output width is bounded by the language size. -/
theorem utility_le_language (v : Vocabulary Φ) (γ : VTask v)
    (h : (correctPolicies v γ).Nonempty) :
    utility v γ h + γ.outputs.card ≤ (language v).card := by
  have hOutputsLeSup :
      γ.outputs.card ≤ (correctPolicies v γ).sup' h (fun π => weakness v π) := by
    rcases h with ⟨π, hπ⟩
    exact (outputs_card_le_weakness_of_mem_correctPolicies hπ).trans (Finset.le_sup' _ hπ)
  have hSupLeLanguage :
      (correctPolicies v γ).sup' h (fun π => weakness v π) ≤ (language v).card := by
    refine Finset.sup'_le (s := correctPolicies v γ) (f := fun π => weakness v π) h ?_
    intro π hπ
    exact weakness_le_language v π
  have hCancel :
      utility v γ h + γ.outputs.card =
        (correctPolicies v γ).sup' h (fun π => weakness v π) := by
    simp [utility, Nat.sub_add_cancel hOutputsLeSup]
  simpa [hCancel] using hSupLeLanguage

end HeytingLean.StackTheory
