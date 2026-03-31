import HeytingLean.VCS.Semilattice
import Mathlib.Order.Heyting.Basic

namespace HeytingLean
namespace VCS

/-- Repository state as a path-indexed multi-value register (CRDT-friendly).
Each path maps to a set of admissible hashes; deterministic states are singleton-valued. -/
abbrev RepoState := String → Set Hash

/-- Order: refinement/containment of admissible hashes at each path. -/
def leState (a b : RepoState) : Prop := a ≤ b

/-- Meet: intersection of admissible hashes per path. -/
def meetState (a b : RepoState) : RepoState := a ⊓ b

/-- Join: union of admissible hashes per path. -/
def joinState (a b : RepoState) : RepoState := a ⊔ b

/-- Heyting implication: pointwise implication inherited from `Set Hash`. -/
def himpState (a b : RepoState) : RepoState := a ⇨ b

/-- Core Heyting law specialized to repository states. -/
theorem le_himp_iff_state (a b c : RepoState) :
    meetState a b ≤ c ↔ a ≤ himpState b c := by
  change a ⊓ b ≤ c ↔ a ≤ b ⇨ c
  exact (le_himp_iff (a := a) (b := b) (c := c)).symm

/-- Derived helper in the form used by phase notes. -/
theorem meet_le_iff (a b c : RepoState) :
    (a ⊓ b ≤ c) ↔ (a ≤ b ⇨ c) := by
  exact (le_himp_iff (a := a) (b := b) (c := c)).symm

end VCS
end HeytingLean
