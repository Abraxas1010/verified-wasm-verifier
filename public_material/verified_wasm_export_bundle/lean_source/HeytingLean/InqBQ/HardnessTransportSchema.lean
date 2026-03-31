import HeytingLean.InqBQ.Computability

namespace HeytingLean
namespace InqBQ

open Nat.Partrec

/--
Pointwise hardness transport on a fixed input family.

This is the honest theorem schema currently supported by the landed InqBQ
non-r.e. endpoint: the source and target predicates live on the same input type
and are related by a pointwise equivalence theorem.
-/
structure PointwiseHardnessBridge (α : Type*) [Primcodable α] where
  sourcePred : α → Prop
  targetPred : α → Prop
  target_iff_source : ∀ a, targetPred a ↔ sourcePred a

/--
Transport non-r.e. across a pointwise equivalence on the same input family.
-/
theorem notRE_of_pointwise_iff
    {α : Type*} [Primcodable α]
    {sourcePred targetPred : α → Prop}
    (hiff : ∀ a, targetPred a ↔ sourcePred a)
    (hSource : ¬ REPred sourcePred) :
    ¬ REPred targetPred := by
  intro hTarget
  exact hSource (REPred.of_eq hTarget hiff)

namespace PointwiseHardnessBridge

variable {α : Type*} [Primcodable α] (B : PointwiseHardnessBridge α)

theorem source_re_of_target_re (hTarget : REPred B.targetPred) :
    REPred B.sourcePred :=
  REPred.of_eq hTarget (fun a => B.target_iff_source a)

theorem target_re_of_source_re (hSource : REPred B.sourcePred) :
    REPred B.targetPred :=
  REPred.of_eq hSource (fun a => (B.target_iff_source a).symm)

theorem target_not_re_of_source_not_re (hSource : ¬ REPred B.sourcePred) :
    ¬ REPred B.targetPred :=
  notRE_of_pointwise_iff B.target_iff_source hSource

theorem source_not_re_of_target_not_re (hTarget : ¬ REPred B.targetPred) :
    ¬ REPred B.sourcePred := by
  intro hSource
  exact hTarget (B.target_re_of_source_re hSource)

end PointwiseHardnessBridge

end InqBQ
end HeytingLean
