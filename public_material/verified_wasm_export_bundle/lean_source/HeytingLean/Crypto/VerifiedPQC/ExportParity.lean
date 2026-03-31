import HeytingLean.Crypto.VerifiedPQC.Programs

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

structure ParityCase where
  passedChecks : Nat
  expectedDecision : Nat
  deriving DecidableEq, Repr

def parityCorpus : List ParityCase :=
  [ { passedChecks := 0, expectedDecision := 0 }
  , { passedChecks := 1, expectedDecision := 0 }
  , { passedChecks := 2, expectedDecision := 0 }
  , { passedChecks := 3, expectedDecision := 0 }
  , { passedChecks := 4, expectedDecision := 1 }
  ]

def parityCaseHolds (c : ParityCase) : Prop :=
  acceptAllChecksFn c.passedChecks = c.expectedDecision

theorem parityCaseHolds_zero :
    parityCaseHolds { passedChecks := 0, expectedDecision := 0 } := by
  simp [parityCaseHolds, acceptAllChecksFn, requiredChecks]

theorem parityCaseHolds_one :
    parityCaseHolds { passedChecks := 1, expectedDecision := 0 } := by
  simp [parityCaseHolds, acceptAllChecksFn, requiredChecks]

theorem parityCaseHolds_two :
    parityCaseHolds { passedChecks := 2, expectedDecision := 0 } := by
  simp [parityCaseHolds, acceptAllChecksFn, requiredChecks]

theorem parityCaseHolds_three :
    parityCaseHolds { passedChecks := 3, expectedDecision := 0 } := by
  simp [parityCaseHolds, acceptAllChecksFn, requiredChecks]

theorem parityCaseHolds_four :
    parityCaseHolds { passedChecks := 4, expectedDecision := 1 } := by
  simp [parityCaseHolds, acceptAllChecksFn, requiredChecks]

theorem parityCorpus_complete :
    ∀ c ∈ parityCorpus, parityCaseHolds c := by
  intro c hc
  simp [parityCorpus, parityCaseHolds, acceptAllChecksFn, requiredChecks] at hc ⊢
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals simp

end VerifiedPQC
end Crypto
end HeytingLean
