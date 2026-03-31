import HeytingLean.PerspectivalPlenum.Enrichment

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

open HeytingLean.PerspectivalPlenum

inductive Obj where
  | a
  | b
  deriving DecidableEq, Repr

def strictLens : Lens.SemanticLens Obj :=
  { profile :=
      { name := "strict"
        contradictionPolicy := Lens.ContradictionPolicy.booleanStrict
        dimension := 2
        languageTag := "test"
        metricTag := "euclidean" }
    witness := fun _ => True
    contradicts := fun
      | Obj.a => True
      | Obj.b => False }

def weightedStrict : Enrichment.WeightedLens Obj ℝ :=
  { lens := strictLens
    weight := fun
      | Obj.a => 0.2
      | Obj.b => 0.8 }

#check Enrichment.Weighting
#check Enrichment.WeightedLens
#check Enrichment.WeightedLensFunctor
#check Enrichment.ProbabilisticWeightedLens

example : Lens.CollapseToBottom strictLens Obj.a := by
  refine Lens.collapse_of_strict_contradiction strictLens Obj.a ?_ ?_ ?_
  · simp [strictLens, Lens.allowsContradictions]
  · simp [strictLens]
  · simp [strictLens]

example : Enrichment.WeightedLens.weightedClaim weightedStrict Obj.a = 0 := by
  have hCollapse : Lens.CollapseToBottom strictLens Obj.a := by
    refine Lens.collapse_of_strict_contradiction strictLens Obj.a ?_ ?_ ?_
    · simp [strictLens, Lens.allowsContradictions]
    · simp [strictLens]
    · simp [strictLens]
  simpa [weightedStrict] using
    Enrichment.WeightedLens.weightedClaim_eq_zero_of_collapse weightedStrict Obj.a hCollapse

example : Enrichment.WeightedLens.weightedClaim weightedStrict Obj.b = 0.8 := by
  have hSat : Lens.LocallySatisfiable strictLens Obj.b := by
    simp [Lens.LocallySatisfiable, strictLens, Lens.allowsContradictions]
  simpa [weightedStrict] using
    Enrichment.WeightedLens.weightedClaim_eq_weight_of_satisfiable weightedStrict Obj.b hSat

end PerspectivalPlenum
end Tests
end HeytingLean
