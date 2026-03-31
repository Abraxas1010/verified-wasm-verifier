import HeytingLean.StackTheory.Stack.Abstractor

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §5: A multi-layer architecture carries a vocabulary, task, and correct policy
at each layer, with the next vocabulary induced by the abstractor. -/
structure Stack (Φ : Type*) [DecidableEq Φ] [Fintype Φ] (n : ℕ) where
  baseVocab : Vocabulary Φ
  task : Fin (n + 1) → UninstantiatedTask Φ
  policy : Fin (n + 1) → Finset (Program Φ)
  vocab : Fin (n + 1) → Vocabulary Φ
  vocab_base : vocab ⟨0, Nat.zero_lt_succ n⟩ = baseVocab
  vocab_step :
    ∀ i : Fin n,
      vocab i.succ = abstractor (vocab i.castSucc) (policy i.castSucc)
  policy_correct :
    ∀ i : Fin (n + 1),
      policy i ∈ correctPolicies (vocab i) (task i (vocab i))

/-- Bennett §5: The instantiated task at layer `i`. -/
def Stack.instantiatedTask (S : Stack Φ n) (i : Fin (n + 1)) : VTask (S.vocab i) :=
  S.task i (S.vocab i)

/-- Bennett §5: Viability means every layer still has at least one correct policy. -/
def Stack.isViable (S : Stack Φ n) : Prop :=
  ∀ i : Fin (n + 1), (correctPolicies (S.vocab i) (S.instantiatedTask i)).Nonempty

end HeytingLean.StackTheory
