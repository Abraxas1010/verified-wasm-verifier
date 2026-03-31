import HeytingLean.ModalCategorySets.Framework.FiniteStateFrames
import HeytingLean.ModalCategorySets.Framework.PureFormulaElimination
import HeytingLean.ModalCategorySets.Validities.ControlCore

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Framework
open HeytingLean.ModalCategorySets.Propositional

theorem partitionFrame_validatesGrzDot2Core (n : Nat) :
    ValidatesGrzDot2Core (partitionFrame n) := by
  letI : Finite (FinPartition n) := HeytingLean.ModalCategorySets.Framework.instFiniteFinPartition n
  intro α p
  have hCore :
      (OrderedFrames.orderFrame (FinPartition n)).Valid (axiomT p) ∧
        (OrderedFrames.orderFrame (FinPartition n)).Valid (axiom4 p) ∧
          (OrderedFrames.orderFrame (FinPartition n)).Valid (axiomDot2 p) ∧
            (OrderedFrames.orderFrame (FinPartition n)).Valid (axiomGrz p) :=
    validatesGrzDot2Core_of_finite_directed_partialOrder
      (W := FinPartition n) (hDir := partitionFrame_directed n) p
  exact hCore

theorem prepartitionFrame_validatesS4Dot2 (n m : Nat) :
    ValidatesS4Dot2 (prepartitionFrame n m) := by
  exact validatesS4Dot2_of_reflexive_transitive_directed
    (prepartitionFrame n m)
    (prepartitionFrame_reflexive n m)
    (prepartitionFrame_transitive n m)
    (prepartitionFrame_directed n m)

end HeytingLean.ModalCategorySets.Validities
