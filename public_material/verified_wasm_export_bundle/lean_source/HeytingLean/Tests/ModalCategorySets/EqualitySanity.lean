import HeytingLean.ModalCategorySets.Framework.EqualityLanguage

namespace HeytingLean.Tests.ModalCategorySets

open HeytingLean.ModalCategorySets.Framework.Equality

def unitValuation : Valuation PUnit := fun _ => PUnit.unit

def finTwoValuation : Valuation (Fin 2)
  | 0 => 0
  | 1 => 1
  | _ => 0

def finTwoPartitionValuation : Valuation (Fin 2)
  | 0 => 0
  | 1 => 0
  | _ => 1

def allFunctionAccessibility : Accessibility := fun {_α} {_β} _ => True

def vars01 : List Nat := 0 :: 1 :: []
def equalPairsWitness : List (Nat × Nat) := Prod.mk 0 1 :: []
def unequalPairsWitness : List (Nat × Nat) := Prod.mk 0 2 :: Prod.mk 1 2 :: []

def pairwiseDistinct01 : EqAssertion := pairwiseDistinct vars01
def partitionWitness : EqAssertion := partitionFormula equalPairsWitness unequalPairsWitness
def exactCardinalityOne : EqAssertion := exactCardinality 1

example : Holds allFunctionAccessibility finTwoValuation pairwiseDistinct01 := by
  change Holds (fun {α β} _ => True) finTwoValuation
    (conjList [EqAssertion.neg (.atomEq 0 1)])
  simp [conjList, Holds, EqAssertion.neg, EqAssertion.top, finTwoValuation]

example : Holds allFunctionAccessibility finTwoPartitionValuation partitionWitness := by
  change Holds (fun {α β} _ => True) finTwoPartitionValuation
      (.conj (conjList [EqAssertion.atomEq 0 1])
        (conjList [EqAssertion.neg (.atomEq 0 2), EqAssertion.neg (.atomEq 1 2)]))
  simp [conjList, Holds, EqAssertion.neg, EqAssertion.top, finTwoPartitionValuation]

example : Holds allFunctionAccessibility unitValuation exactCardinalityOne := by
  change Holds (fun {α β} _ => True) unitValuation
      (.conj (.existsQ (conjList []))
        (.forallQ (.forallQ (disjList [EqAssertion.atomEq 0 1]))))
  constructor
  · exact ⟨PUnit.unit, by simp [conjList, Holds, EqAssertion.top]⟩
  · intro a b
    simp [disjList, Holds]

end HeytingLean.Tests.ModalCategorySets
