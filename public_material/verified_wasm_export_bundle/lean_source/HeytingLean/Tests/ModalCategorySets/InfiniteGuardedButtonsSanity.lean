import HeytingLean.ModalCategorySets.Framework.InfiniteGuardedButtons

namespace HeytingLean.Tests.ModalCategorySets

open HeytingLean.ModalCategorySets.Framework

example :
    Nonempty (HeytingLean.ModalCategorySets.Framework.Buttons.AllGuardedButtonPatternWitness
      (ρ := infinitePartitionWitnessValuationLift
        (HeytingLean.ModalCategorySets.Framework.Buttons.patternPartition 2
          ({(0 : Fin 2)} : Finset (Fin 2))))
      (s := (({(0 : Fin 2)} : Finset (Fin 2)) ∪ ({(1 : Fin 2)} : Finset (Fin 2))))) := by
  refine HeytingLean.ModalCategorySets.Framework.Buttons.exists_allFunctions_guardedButton_pattern_above
    (ρ := infinitePartitionWitnessValuationLift
      (HeytingLean.ModalCategorySets.Framework.Buttons.patternPartition 2
        ({(0 : Fin 2)} : Finset (Fin 2))))
    (s := ({(0 : Fin 2)} : Finset (Fin 2)))
    (t := (({(0 : Fin 2)} : Finset (Fin 2)) ∪ ({(1 : Fin 2)} : Finset (Fin 2)))) ?_ ?_
  · exact realizedPartition_infinitePartitionWitnessValuationLift
      (HeytingLean.ModalCategorySets.Framework.Buttons.patternPartition 2
        ({(0 : Fin 2)} : Finset (Fin 2)))
  · intro i hi
    simp at hi
    simp [hi]

example :
    Nonempty (HeytingLean.ModalCategorySets.Framework.Buttons.SurjGuardedButtonPatternWitness
      (ρ := infinitePartitionWitnessValuationLift
        (HeytingLean.ModalCategorySets.Framework.Buttons.patternPartition 2
          ({(0 : Fin 2)} : Finset (Fin 2))))
      (s := (({(0 : Fin 2)} : Finset (Fin 2)) ∪ ({(1 : Fin 2)} : Finset (Fin 2))))) := by
  refine HeytingLean.ModalCategorySets.Framework.Buttons.exists_surjections_guardedButton_pattern_above
    (ρ := infinitePartitionWitnessValuationLift
      (HeytingLean.ModalCategorySets.Framework.Buttons.patternPartition 2
        ({(0 : Fin 2)} : Finset (Fin 2))))
    (s := ({(0 : Fin 2)} : Finset (Fin 2)))
    (t := (({(0 : Fin 2)} : Finset (Fin 2)) ∪ ({(1 : Fin 2)} : Finset (Fin 2)))) ?_ ?_
  · exact realizedPartition_infinitePartitionWitnessValuationLift
      (HeytingLean.ModalCategorySets.Framework.Buttons.patternPartition 2
        ({(0 : Fin 2)} : Finset (Fin 2)))
  · intro i hi
    simp at hi
    simp [hi]

end HeytingLean.Tests.ModalCategorySets
