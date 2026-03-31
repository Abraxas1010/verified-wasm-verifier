import HeytingLean.ModalCategorySets.Framework.EqualityMorphismBridge

namespace HeytingLean.Tests.ModalCategorySets

open HeytingLean.ModalCategorySets.Framework.Equality
open HeytingLean.ModalCategorySets.Framework

def finTwoValuationBridge : Valuation (Fin 2)
  | 0 => 0
  | 1 => 1
  | _ => 0

example : HoldsIn allFunctions finTwoValuationBridge (.atomEq 0 0) := by
  rfl

example : HoldsIn bijections finTwoValuationBridge (.diaQ (.atomEq 0 0)) := by
  show Holds bijections.admits finTwoValuationBridge (.diaQ (.atomEq 0 0))
  refine Exists.intro (Fin 2) ?_
  refine Exists.intro (id : Fin 2 → Fin 2) ?_
  constructor
  · exact Function.bijective_id
  · rfl

end HeytingLean.Tests.ModalCategorySets
