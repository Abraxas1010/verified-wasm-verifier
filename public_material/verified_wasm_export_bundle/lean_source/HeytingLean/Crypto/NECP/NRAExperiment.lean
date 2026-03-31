namespace HeytingLean
namespace Crypto
namespace NECP

universe u v w

/-- Abstract nucleus-recovery experiment surface. -/
structure NRAExperiment (Secret : Type u) (Pub : Type v) (Guess : Type w) where
  encode : Secret → Pub
  solvedBy : Guess → Secret → Prop

namespace NRAExperiment

variable {Secret : Type u} {Pub : Type v} {Guess : Type w}

/-- Explicit adversary interface with a query budget and a recovery procedure. -/
structure Adversary (E : NRAExperiment Secret Pub Guess) where
  queryBudget : Nat
  solve : Pub → Guess

/-- The adversary wins if it solves every encoded secret instance. -/
def wins (E : NRAExperiment Secret Pub Guess) (A : Adversary E) : Prop :=
  ∀ s, E.solvedBy (A.solve (E.encode s)) s

/-- Named NECP-facing alias for the adversary surface used in hardness theorems. -/
abbrev NRAAdversary (E : NRAExperiment Secret Pub Guess) := Adversary E

/-- NRA hardness: no adversary wins the abstract experiment. -/
def Hard (E : NRAExperiment Secret Pub Guess) : Prop :=
  ¬ ∃ A : Adversary E, wins E A

theorem hard_of_no_winning_adversary (E : NRAExperiment Secret Pub Guess)
    (h : ∀ A : Adversary E, ¬ wins E A) : Hard E := by
  intro hw
  rcases hw with ⟨A, hA⟩
  exact h A hA

end NRAExperiment

end NECP
end Crypto
end HeytingLean
