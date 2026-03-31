import HeytingLean.Crypto.ConstructiveHardness.TaskSpec

/-!
# CT Protocol composition lemmas

This file provides small generic lemmas to support compositional security proofs:
* A simple way to combine task specifications.
* An “at least one component is impossible” lemma for serial composition (classical).
* A generic “requires an impossible subtask ⇒ impossible” lemma.
-/

namespace HeytingLean
namespace Crypto
namespace ConstructiveHardness

open HeytingLean.Constructor.CT

universe u

namespace TaskSpec

/-- Combine two task specifications by conjunction on their predicates. -/
def seq {σ : Type u} {CT : TaskCT σ}
    (TS₁ TS₂ : TaskSpec σ CT) : TaskSpec σ CT where
  Spec T := TS₁.Spec T ∧ TS₂.Spec T
  sound T hT := ⟨TS₁.sound T hT, TS₂.sound T hT⟩

end TaskSpec

/-- If a serial composition is impossible, then at least one component is impossible.

This is the classical contrapositive of `TaskCT.possible_seq`. -/
theorem impossible_seq_of_impossible
    {σ : Type u} {CT : TaskCT σ} {T U : HeytingLean.Constructor.CT.Task σ} :
    CT.impossible (HeytingLean.Constructor.CT.Task.seq T U) →
      CT.impossible T ∨ CT.impossible U := by
  classical
  intro hImpossible
  by_contra h
  have h' : ¬ CT.impossible T ∧ ¬ CT.impossible U := by
    simpa [not_or] using h
  have hPossibleT : CT.possible T := by
    -- `CT.impossible T` is `¬ CT.possible T`
    simpa [TaskCT.impossible] using (not_not.mp h'.1)
  have hPossibleU : CT.possible U := by
    simpa [TaskCT.impossible] using (not_not.mp h'.2)
  have hPossibleSeq : CT.possible (HeytingLean.Constructor.CT.Task.seq T U) :=
    CT.possible_seq hPossibleT hPossibleU
  exact hImpossible hPossibleSeq

/-- Security transfer lemma: if any successful attack would make an impossible subtask possible,
then the attack itself is impossible. -/
theorem composed_security
    {σ : Type u} {CT : TaskCT σ}
    {T_attack T_sub : HeytingLean.Constructor.CT.Task σ}
    (h_requires : CT.possible T_attack → CT.possible T_sub)
    (h_sub_impossible : CT.impossible T_sub) :
    CT.impossible T_attack := by
  intro hPossible
  exact h_sub_impossible (h_requires hPossible)

end ConstructiveHardness
end Crypto
end HeytingLean

