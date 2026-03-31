import HeytingLean.ModalCategorySets.Framework.FiniteTranslation
import HeytingLean.ModalCategorySets.Framework.FiniteStateFrames
import HeytingLean.ModalCategorySets.Framework.FiniteCorrespondence
import HeytingLean.ModalCategorySets.Framework.PartitionFormulas
import HeytingLean.ModalCategorySets.Framework.PartitionModalCorrespondence
import HeytingLean.ModalCategorySets.Framework.PureFormulaElimination
import HeytingLean.ModalCategorySets.Framework.FiniteSententialCorrespondence
import HeytingLean.ModalCategorySets.Validities.PaperRows

namespace HeytingLean.Tests.ModalCategorySets

open HeytingLean.ModalCategorySets.Framework
open HeytingLean.ModalCategorySets.Framework.Equality
open HeytingLean.ModalCategorySets.Validities

def allFunctionAccessibility : Accessibility := fun {_α} {_β} _ => True

def unitValuation : Valuation PUnit := fun _ => PUnit.unit

def finTwoValuation : Valuation (Fin 2)
  | 0 => 0
  | 1 => 1
  | _ => 0

private theorem realizedPartition_finTwoValuation :
    realizedPartition finTwoValuation 2 = discretePartition 2 := by
  ext i j
  fin_cases i <;> fin_cases j
  · change finTwoValuation 0 = finTwoValuation 0 ↔ ((0 : Fin 2) = 0)
    simp [finTwoValuation]
  · change finTwoValuation 0 = finTwoValuation 1 ↔ ((0 : Fin 2) = 1)
    simp [finTwoValuation]
  · change finTwoValuation 1 = finTwoValuation 0 ↔ ((1 : Fin 2) = 0)
    simp [finTwoValuation]
  · change finTwoValuation 1 = finTwoValuation 1 ↔ ((1 : Fin 2) = 1)
    simp [finTwoValuation]

example :
    Holds allFunctionAccessibility unitValuation (exactCardinality 1) := by
  exact (holds_exactCardinality_iff_fintype_card_eq
    (admits := allFunctionAccessibility) (ρ := unitValuation) 1).mpr rfl

example :
    Holds allFunctionAccessibility finTwoValuation (exactCardinality 2) := by
  exact (holds_exactCardinality_iff_fintype_card_eq
    (admits := allFunctionAccessibility) (ρ := finTwoValuation) 2).mpr rfl

example :
    Refines (discretePartition 2) (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) := by
  intro i j hij
  trivial

example :
    (partitionFrame 2).rel (discretePartition 2)
      (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) := by
  intro i j hij
  trivial

example :
    (lollipopFrame 3).rel (lollipopRoot 3) (.cluster 0) := by
  trivial

example :
    Refines (discretePartition 2) (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) ↔
      Nonempty {f : PartitionWorld (discretePartition 2) →
          PartitionWorld (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) //
        Function.Surjective f ∧
          PartitionTupleMap f} := by
  symm
  exact exists_surjective_partition_map_iff_refines

example :
    Nonempty {f : PrepartitionWorld (discretePartition 2) 1 →
        PrepartitionWorld (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) 3 //
      PrepartitionTupleMap f} := by
  exact (exists_prepartition_map_iff_refines (n := 2) (k := 1) (l := 3)
    (by decide)
    (P := discretePartition 2)
    (Q := kernelPartition (fun _ : Fin 2 => (0 : Fin 2)))).2 (by
      intro i j hij
      trivial)

example :
    surjections.toKripkeCategory.toFrame.rel (surjectionLineWorld 4 0) (surjectionLineWorld 4 2) := by
  have h : (0 : Fin 4) ≤ 2 := by simp
  exact (surjectionLineWorld_rel_iff (n := 4) 0 2).2 h

example :
    ¬ surjections.toKripkeCategory.toFrame.rel (surjectionLineWorld 4 2) (surjectionLineWorld 4 0) := by
  intro h
  have : (2 : Fin 4) ≤ 0 := (surjectionLineWorld_rel_iff (n := 4) 2 0).1 h
  omega

example :
    allFunctions.toKripkeCategory.toFrame.rel
      (lollipopWitnessWorld 3 (lollipopRoot 3))
      (lollipopWitnessWorld 3 (.cluster 2)) := by
  exact (lollipopWitnessWorld_rel_iff 3 (lollipopRoot 3) (.cluster 2)).2 trivial

example :
    ¬ allFunctions.toKripkeCategory.toFrame.rel
      (lollipopWitnessWorld 3 (.cluster 1))
      (lollipopWitnessWorld 3 (lollipopRoot 3)) := by
  intro h
  have : (lollipopFrame 3).rel (.cluster 1) (lollipopRoot 3) :=
    (lollipopWitnessWorld_rel_iff 3 (.cluster 1) (lollipopRoot 3)).1 h
  cases this

example :
    surjections.toKripkeCategory.toFrame.rel (surjectionLineWorld 4 1) (surjectionLineWorld 4 3) ↔
      (surjectionLineFrame 4).rel 1 3 :=
  grz3j_n_row_rel_iff 1 3

example :
    RealizesCardinalityLabel (surjectionLineWorld 4 2) (surjectionLineLabel 4 2) :=
  grz3j_n_row_realizes_label 2

example :
    HoldsIn surjections finTwoValuation (exactCardinality 2) ↔ Fintype.card (Fin 2) = 2 :=
  grz3j_n_row_exactCardinality_iff (α := Fin 2) (n := 2) finTwoValuation (0 : Fin 2)

example :
    allFunctions.toKripkeCategory.toFrame.rel
      (lollipopWitnessWorld 3 (.cluster 1))
      (lollipopWitnessWorld 3 (.cluster 2)) ↔
      (lollipopFrame 3).rel (.cluster 1) (.cluster 2) :=
  lollipop_row_rel_iff 3 (.cluster 1) (.cluster 2)

example :
    RealizesCardinalityLabel (lollipopWitnessWorld 3 (.cluster 2)) (lollipopLabel 3 (.cluster 2)) :=
  lollipop_row_realizes_label 3 (.cluster 2)

example :
    Nonempty {f : PartitionWorld (discretePartition 2) →
        PartitionWorld (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) //
      Function.Surjective f ∧ PartitionTupleMap f} ↔
      Refines (discretePartition 2) (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) :=
  partition_n_row_iff_refines

example :
    Nonempty {f : PrepartitionWorld (discretePartition 2) 1 →
        PrepartitionWorld (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) 3 //
      PrepartitionTupleMap f} ↔
      Refines (discretePartition 2) (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) :=
  prepartition_n_row_iff_refines (n := 2) (k := 1) (l := 3) (by decide)

example :
    Holds allFunctionAccessibility
      (partitionWitnessValuation (discretePartition 2))
      (partitionFormulaOf (discretePartition 2)) :=
  holds_partitionFormulaOf_partitionWitnessValuation (admits := allFunctionAccessibility)
    (discretePartition 2)

example :
    HoldsIn allFunctions
      (partitionWitnessValuation (discretePartition 2))
      (EqAssertion.diaQ
        (partitionFormulaOf (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))))) ↔
      Refines (discretePartition 2) (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) :=
  allFunctions_dia_partitionFormulaOf_iff_refines

example :
    HoldsIn surjections
      (partitionWitnessValuation (discretePartition 2))
      (EqAssertion.diaQ
        (partitionFormulaOf (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))))) ↔
      Refines (discretePartition 2) (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) :=
  surjections_dia_partitionFormulaOf_iff_refines

example :
    HoldsIn surjections
      (partitionWitnessValuation (discretePartition 2))
      (EqAssertion.diaQ
        (partitionFormulaOf (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))))) := by
  exact surjections_dia_partitionFormulaOf_iff_refines.2 (by
    intro i j hij
    trivial)

example :
    HoldsIn allFunctions finTwoValuation
      (partitionFormulaOf (discretePartition 2)) := by
  apply (holds_partitionFormulaOf_iff_realizedPartition
    (admits := allFunctionAccessibility)
    (ρ := finTwoValuation)
    (P := discretePartition 2)).mpr
  exact realizedPartition_finTwoValuation

example :
    HoldsIn allFunctions finTwoValuation
      (EqAssertion.diaQ
        (partitionFormulaOf (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))))) ↔
      Refines (discretePartition 2) (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) := by
  apply allFunctions_dia_partitionFormulaOf_iff_refines_of_holds
  apply (holds_partitionFormulaOf_iff_realizedPartition
    (admits := allFunctionAccessibility)
    (ρ := finTwoValuation)
    (P := discretePartition 2)).mpr
  exact realizedPartition_finTwoValuation

example :
    HoldsIn surjections finTwoValuation
      (EqAssertion.diaQ
        (partitionFormulaOf (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))))) ↔
      Refines (discretePartition 2) (kernelPartition (fun _ : Fin 2 => (0 : Fin 2))) := by
  apply surjections_dia_partitionFormulaOf_iff_refines_of_holds (hn := by decide) (ρ := finTwoValuation)
  apply (holds_partitionFormulaOf_iff_realizedPartition
    (admits := surjections.admits)
    (ρ := finTwoValuation)
    (P := discretePartition 2)).mpr
  exact realizedPartition_finTwoValuation

example :
    HoldsIn allFunctions finTwoValuation
      (purePartitionElim 2 (EqAssertion.neg (.atomEq 0 1))) ↔
      HoldsIn allFunctions finTwoValuation
        (EqAssertion.neg (.atomEq 0 1)) := by
  have hPure : Equality.IsPure (EqAssertion.neg (.atomEq 0 1)) := by
    exact And.intro trivial trivial
  have hUses : Equality.UsesOnlyLT 2 (EqAssertion.neg (.atomEq 0 1)) := by
    exact And.intro (And.intro (by decide) (by decide)) trivial
  simpa using
    (holds_purePartitionElim_iff
      (admits := allFunctions.admits)
      (ρ := finTwoValuation)
      (n := 2)
      (φ := EqAssertion.neg (.atomEq 0 1))
      hPure
      hUses)

example :
    HoldsIn surjections finTwoValuation
      (EqAssertion.diaQ (EqAssertion.neg (.atomEq 0 1))) ↔
      HoldsIn surjections finTwoValuation
        (EqAssertion.diaQ (purePartitionElim 2 (EqAssertion.neg (.atomEq 0 1)))) := by
  have hPure : Equality.IsPure (EqAssertion.neg (.atomEq 0 1)) := by
    exact And.intro trivial trivial
  have hUses : Equality.UsesOnlyLT 2 (EqAssertion.neg (.atomEq 0 1)) := by
    exact And.intro (And.intro (by decide) (by decide)) trivial
  simpa using
    (holds_dia_purePartitionElim_iff
      (M := surjections)
      (ρ := finTwoValuation)
      (n := 2)
      (φ := EqAssertion.neg (.atomEq 0 1))
      hPure
      hUses)

end HeytingLean.Tests.ModalCategorySets
