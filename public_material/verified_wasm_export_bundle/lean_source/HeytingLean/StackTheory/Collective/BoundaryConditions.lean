import Mathlib.Data.Fintype.Basic
import HeytingLean.StackTheory.Collective.Identity

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §6: Boundary conditions restrict each component policy set. -/
structure BoundaryConditions {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v) where
  restricted : (j : Fin m) → Finset (Finset (Program Φ))
  sub : ∀ j, restricted j ⊆ correctPolicies v (parts j)

/-- Bennett §6: The collectively admissible policies under the boundary conditions. -/
def restrictedCollective {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts) : Finset (Finset (Program Φ)) :=
  (language v).filter (fun π => ∀ j : Fin m, π ∈ bc.restricted j)

/-- Bennett §6: Over-constraint means the restricted collective set is empty. -/
def isOverConstrained {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts) : Prop :=
  restrictedCollective v parts bc = ∅

/-- Bennett §6: The parts for which a candidate policy remains feasible. -/
def feasibleParts {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts) (π : Finset (Program Φ)) : Finset (Fin m) :=
  Finset.univ.filter (fun j => π ∈ bc.restricted j)

/-- Bennett §6: A splinter is a nonempty proper subset with a common feasible policy. -/
def isSplinter {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts) (S : Finset (Fin m)) : Prop :=
  S.Nonempty ∧ S ⊂ Finset.univ ∧
    ((language v).filter (fun π => ∀ j ∈ S, π ∈ bc.restricted j)).Nonempty

end HeytingLean.StackTheory
