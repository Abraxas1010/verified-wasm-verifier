import Mathlib.Order.Nucleus

/-!
# Bridge.Veselov.MultiAgentNucleus

Scoped OP04 bridge surface for finite-family multi-agent nuclei.
This module is intentionally contract-first and finite-class only.
-/

namespace HeytingLean.Bridge.Veselov

universe u v

/-- Finite family of agent nuclei with an explicit composed nucleus contract. -/
structure FiniteAgentNucleusFamily (α : Type u) (n : Nat) where
  agentNucleus : Fin n → Nucleus (Set α)
  combinedNucleus : Nucleus (Set α)
  refinesCombined :
    ∀ i : Fin n, ∀ U : Set α, agentNucleus i U ⊆ combinedNucleus U
  combinedFixedOfAgentsFixed :
    ∀ U : Set α, (∀ i : Fin n, agentNucleus i U = U) → combinedNucleus U = U

/-- A set is fixed by every agent nucleus in the finite family. -/
def MultiAgentFixed {α : Type u} {n : Nat}
    (F : FiniteAgentNucleusFamily α n) (U : Set α) : Prop :=
  ∀ i : Fin n, F.agentNucleus i U = U

/-- OP04 core theorem: finite-family fixedness implies composed fixedness. -/
theorem finite_family_composition_theorem
    {α : Type u} {n : Nat}
    (F : FiniteAgentNucleusFamily α n) (U : Set α) :
    MultiAgentFixed F U → F.combinedNucleus U = U := by
  intro hfixed
  exact F.combinedFixedOfAgentsFixed U hfixed

/-- Optional transport contract for cross-carrier preservation checks. -/
structure MultiAgentTransportContract
    (α : Type u) (β : Type v) (n : Nat)
    (F : FiniteAgentNucleusFamily α n) where
  transport : α → β
  preserveAgent :
    ∀ i : Fin n, ∀ U : Set α,
      transport '' (F.agentNucleus i U) ⊆ transport '' U
  preserveCombined :
    ∀ U : Set α,
      transport '' (F.combinedNucleus U) ⊆ transport '' U

/-- Cross-agent preservation theorem from the explicit transport contract. -/
theorem multi_agent_transport_preservation
    {α : Type u} {β : Type v} {n : Nat}
    (F : FiniteAgentNucleusFamily α n)
    (T : MultiAgentTransportContract α β n F)
    (U : Set α) :
    T.transport '' (F.combinedNucleus U) ⊆ T.transport '' U :=
  T.preserveCombined U

/--
Packaged OP04 scoped theorem:
- finite-family composition closes in the combined nucleus,
- and transport preservation is available via explicit contract.
-/
theorem op04_scoped_bridge_theorem
    {α : Type u} {β : Type v} {n : Nat}
    (F : FiniteAgentNucleusFamily α n)
    (T : MultiAgentTransportContract α β n F)
    (U : Set α) :
    (MultiAgentFixed F U → F.combinedNucleus U = U) ∧
      (T.transport '' (F.combinedNucleus U) ⊆ T.transport '' U) := by
  exact ⟨finite_family_composition_theorem (F := F) (U := U),
    multi_agent_transport_preservation (F := F) T U⟩

end HeytingLean.Bridge.Veselov
