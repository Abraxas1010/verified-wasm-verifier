import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import HeytingLean.StackTheory.Stack.LawOfTheStack
import HeytingLean.StackTheory.Collective.CancerAnalogue

namespace HeytingLean.StackTheory.Applications

open HeytingLean.StackTheory

/-- Bennett §6 application: a tiny concrete state space for the HALO delegation example. -/
inductive HaloState
  | tool
  | proof
  deriving DecidableEq

instance : Fintype HaloState where
  elems := {HaloState.tool, HaloState.proof}
  complete := by
    intro x
    cases x <;> simp

/-- Bennett §6 application: concrete vocabulary for the two-state HALO toy model. -/
def haloBaseVocabulary : Vocabulary HaloState :=
  { ({HaloState.tool} : Finset HaloState), ({HaloState.proof} : Finset HaloState) }

/-- Bennett §6 application: a permissive task whose outputs are exactly the ambient language. -/
def permissiveTask (v : Vocabulary HaloState) : VTask v where
  inputs := {∅}
  outputs := language v
  outputs_sub := by
    intro o ho
    simpa [extension] using ho

/-- Bennett §6 application: the empty policy is correct for the permissive task. -/
theorem empty_policy_correct (v : Vocabulary HaloState) :
    (∅ : Finset (Program HaloState)) ∈ correctPolicies v (permissiveTask v) := by
  refine Finset.mem_filter.mpr ?_
  constructor
  · rw [mem_language]
    constructor
    · simp
    · rw [truthSet_empty]
      exact ⟨HaloState.tool, Fintype.complete HaloState.tool⟩
  · ext o
    simp [permissiveTask, extension]

/-- Bennett §6 application: the concrete HALO policy is the weakest policy on each layer. -/
def haloPolicy : Fin 2 → Finset (Program HaloState) := fun _ => ∅

/-- Bennett §6 application: the HALO task family reuses the permissive task at each layer. -/
def haloTask : Fin 2 → UninstantiatedTask HaloState := fun _ v => permissiveTask v

/-- Bennett §6 application: the induced vocabulary chain for the two-layer HALO model. -/
def haloVocabulary : Fin 2 → Vocabulary HaloState
  | ⟨0, _⟩ => haloBaseVocabulary
  | ⟨1, _⟩ => abstractor haloBaseVocabulary ∅

/-- Bennett §6 application: a concrete two-layer stack for the HALO delegation picture. -/
def haloStack : Stack HaloState 1 where
  baseVocab := haloBaseVocabulary
  task := haloTask
  policy := haloPolicy
  vocab := haloVocabulary
  vocab_base := rfl
  vocab_step := by
    intro i
    have hi : i = ⟨0, by decide⟩ := by
      apply Fin.ext
      omega
    subst hi
    rfl
  policy_correct := by
    intro i
    have hi : i.1 = 0 ∨ i.1 = 1 := by
      omega
    rcases hi with hi | hi
    · have hi' : i = ⟨0, by decide⟩ := by
        apply Fin.ext
        simpa using hi
      subst hi'
      simpa [haloTask, haloPolicy, haloVocabulary] using empty_policy_correct haloBaseVocabulary
    · have hi' : i = ⟨1, by decide⟩ := by
        apply Fin.ext
        simpa using hi
      subst hi'
      simpa [haloTask, haloPolicy, haloVocabulary] using
        empty_policy_correct (abstractor haloBaseVocabulary ∅)

/-- Bennett §6 application: the concrete HALO stack is viable at both layers. -/
theorem halo_viable : haloStack.isViable := by
  intro i
  have hi : i.1 = 0 ∨ i.1 = 1 := by
    omega
  rcases hi with hi | hi
  · have hi' : i = ⟨0, by decide⟩ := by
      apply Fin.ext
      simpa using hi
    subst hi'
    refine ⟨∅, ?_⟩
    simpa [haloStack, haloTask, haloPolicy, haloVocabulary] using
      empty_policy_correct haloBaseVocabulary
  · have hi' : i = ⟨1, by decide⟩ := by
      apply Fin.ext
      simpa using hi
    subst hi'
    refine ⟨∅, ?_⟩
    simpa [haloStack, haloTask, haloPolicy, haloVocabulary] using
      empty_policy_correct (abstractor haloBaseVocabulary ∅)

/-- Bennett §6 application: concrete AgentHALO instance of Bennett's Law of the Stack. -/
theorem halo_agent_bound :
    utility (haloStack.vocab ⟨1, by decide⟩)
        (haloStack.instantiatedTask ⟨1, by decide⟩)
        (halo_viable ⟨1, by decide⟩)
      + (haloStack.instantiatedTask ⟨1, by decide⟩).outputs.card
      ≤ 2 ^ (extension (haloStack.vocab ⟨0, by decide⟩)
          (haloStack.policy ⟨0, by decide⟩)).card := by
  simpa using
    law_of_the_stack haloStack ⟨0, by decide⟩ (halo_viable ⟨1, by decide⟩)

end HeytingLean.StackTheory.Applications
