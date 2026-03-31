import HeytingLean.ATP.Ensemble.SkeletonExtract

namespace HeytingLean
namespace ATP
namespace Ensemble

open PTS.BaseExtension

def hh_search (fuel : Nat) (P : Program) (s : GoalSkeleton) : Bool :=
  search fuel P (encode s.toIPL)

example : hh_search 5 [] (extractIdentity ⟨0⟩) = true := by
  native_decide

end Ensemble
end ATP
end HeytingLean
