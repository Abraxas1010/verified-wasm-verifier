import HeytingLean.ModalCategorySets.Validities.Pointed
import HeytingLean.ModalCategorySets.Framework.TypeWorlds

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional
open HeytingLean.ModalCategorySets.Framework

universe u

theorem nonemptyFunctions_validateAt_S5 (X : Framework.NonemptyType) :
    ModalTheory.ValidatesAt nonemptyFunctionsCategory.toFrame X .S5 :=
  validatesAtS5_of_coneInvertible nonemptyFunctionsCategory X
    (nonemptyFunctions_coneInvertibleAt X)

theorem nonemptyFunctions_frame_euclidean :
    Euclidean nonemptyFunctionsCategory.toFrame := by
  intro X Y Z hXY hXZ
  exact nonemptyFunctions_rel Y Z

theorem nonemptyFunctions_validate_S5 :
    ModalTheory.Validates nonemptyFunctionsCategory.toFrame .S5 :=
  validatesS5_of_reflexive_transitive_euclidean
    nonemptyFunctionsCategory.toFrame
    (KripkeCategory.frame_reflexive (C := nonemptyFunctionsCategory))
    (KripkeCategory.frame_transitive (C := nonemptyFunctionsCategory))
    nonemptyFunctions_frame_euclidean

end HeytingLean.ModalCategorySets.Validities
