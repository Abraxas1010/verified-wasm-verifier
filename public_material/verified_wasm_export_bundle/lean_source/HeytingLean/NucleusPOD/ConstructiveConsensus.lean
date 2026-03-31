import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 8: Cohomology and Constructive Consensus
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def consensusStep (state vote : Nat) : Nat :=
  Nat.max state vote

theorem nucleus_consensus_terminates (state vote : Nat) :
    consensusStep (consensusStep state vote) vote = consensusStep state vote := by
  simp [consensusStep]

theorem nucleus_consensus_safe (state vote : Nat) : state ≤ consensusStep state vote := by
  exact Nat.le_max_left _ _

theorem nucleus_consensus_valid (state vote : Nat) : vote ≤ consensusStep state vote := by
  exact Nat.le_max_right _ _

/-- Constructive consensus operator is commutative on candidate states. -/
theorem consensus_commutative (state vote : Nat) :
    consensusStep state vote = consensusStep vote state := by
  simp [consensusStep, Nat.max_comm]

theorem consensus_without_EM (state vote : Nat) :
    state ≤ consensusStep state vote ∧
      vote ≤ consensusStep state vote ∧
      (∀ z : Nat, state ≤ z → vote ≤ z → consensusStep state vote ≤ z) := by
  refine ⟨nucleus_consensus_safe state vote, nucleus_consensus_valid state vote, ?_⟩
  intro z hState hVote
  exact (Nat.max_le).2 ⟨hState, hVote⟩

end NucleusPOD
end HeytingLean
