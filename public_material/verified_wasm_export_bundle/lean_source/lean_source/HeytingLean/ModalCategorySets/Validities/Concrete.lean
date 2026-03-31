import HeytingLean.ModalCategorySets.Propositional.Theories

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional
open HeytingLean.ModalCategorySets.Framework

theorem allFunctions_validate_K :
    ModalTheory.Validates (allFunctions.toKripkeCategory.toFrame) .K :=
  validatesK _

theorem surjections_validate_S4 :
    ModalTheory.Validates (surjections.toKripkeCategory.toFrame) .S4 :=
  s4_valid_in_kripke_category _

theorem injections_validate_S4 :
    ModalTheory.Validates (injections.toKripkeCategory.toFrame) .S4 :=
  s4_valid_in_kripke_category _

theorem bijections_validate_S5 :
    ModalTheory.Validates (bijections.toKripkeCategory.toFrame) .S5 :=
  s5_valid_on_bijections

theorem identityCategory_validate_Triv :
    ModalTheory.Validates identityCategory.toFrame .Triv := by
  intro α p
  exact triv_valid_on_identityCategory p

end HeytingLean.ModalCategorySets.Validities
