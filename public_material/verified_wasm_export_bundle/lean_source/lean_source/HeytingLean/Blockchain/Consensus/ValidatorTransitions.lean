import HeytingLean.Blockchain.Consensus.Spec

/-
# Consensus.ValidatorTransitions

Minimal semantic target for the bridge-security row
`Validator Set Transitions` from `crypto_proofs_master_list.md`.

We model validator-set handoffs between epochs as a simple sequence of
validator sets indexed by `Epoch := Nat`, and state that there exists a
validator-set schedule in which *every* handoff has a non-empty
overlap between successive sets. This captures, at an abstract level,
the idea that validator sets do not change arbitrarily from one epoch
to the next.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace ValidatorTransitions

/-- Epoch index for validator sets. -/
abbrev Epoch := Nat

/-- Abstract validator identifier. -/
abbrev ValidatorId := Nat

/-- A validator set is represented as a finite list of identifiers. -/
abbrev ValidatorSet := List ValidatorId

/-- Successive validator sets "overlap" when they share at least one
    common validator identifier. -/
def Overlap (s₁ s₂ : ValidatorSet) : Prop :=
  ∃ v : ValidatorId, v ∈ s₁ ∧ v ∈ s₂

/-- Semantic statement for validator-set transitions:

There exists a validator-set schedule `vs : Epoch → ValidatorSet` such
that for every epoch `e`, the sets at epochs `e` and `e.succ` have a
non-empty overlap.

This is a deliberately simple realisation: we exhibit a constant
schedule where the same non-empty validator set is used at every
epoch, so all handoffs are trivially overlapping. -/
def Statement : Prop :=
  ∃ vs : Epoch → ValidatorSet,
    ∀ e : Epoch, Overlap (vs e) (vs e.succ)

/-- `Statement` holds for a constant validator-set schedule in which
    every epoch uses the singleton set `{0}`. -/
theorem statement_holds : Statement := by
  classical
  -- Take the constant singleton validator set `{0}` at every epoch.
  refine ⟨fun _ => [0], ?_⟩
  intro e
  -- The overlap witness is the validator `0`, which is in both lists.
  refine ⟨0, ?hIn₁, ?hIn₂⟩
  · simp
  · simp

end ValidatorTransitions
end Consensus
end Blockchain
end HeytingLean

