import Mathlib.Data.Fintype.Basic
import HeytingLean.StackTheory.Primitives.Task

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §5: The collective policy set is the finite intersection of the component
policy sets inside the ambient language. -/
def collectivePolicies {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v) :
    Finset (Finset (Program Φ)) :=
  (language v).filter (fun π => ∀ j : Fin m, π ∈ correctPolicies v (parts j))

/-- Bennett §5: Collective identity exists exactly when the collective policy set is nonempty. -/
def hasCollectiveIdentity {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v) : Prop :=
  (collectivePolicies v parts).Nonempty

end HeytingLean.StackTheory
