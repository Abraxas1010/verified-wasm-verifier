import HeytingLean.PerspectivalPlenum.Enrichment.Weights
import HeytingLean.PerspectivalPlenum.Lens.Collapse

namespace HeytingLean
namespace PerspectivalPlenum
namespace Enrichment

universe u v w

/-- A semiring-weighted lens interpretation. -/
structure WeightedLens (α : Type u) (W : Type v) [Semiring W] where
  lens : Lens.SemanticLens α
  weight : α → W

namespace WeightedLens

variable {α : Type u} {W : Type v} [Semiring W]

/-- Weighted local claim: returns object weight when locally satisfiable, else `0`. -/
noncomputable def weightedClaim (L : WeightedLens α W) (x : α) : W := by
  classical
  exact if Lens.LocallySatisfiable L.lens x then L.weight x else 0

/-- Weighted local collapse: returns object weight when collapsed, else `0`. -/
noncomputable def weightedCollapse (L : WeightedLens α W) (x : α) : W := by
  classical
  exact if Lens.CollapseToBottom L.lens x then L.weight x else 0

@[simp] theorem weightedClaim_eq_weight_of_satisfiable
    (L : WeightedLens α W) (x : α) (h : Lens.LocallySatisfiable L.lens x) :
    weightedClaim L x = L.weight x := by
  classical
  dsimp [weightedClaim]
  exact if_pos h

@[simp] theorem weightedClaim_eq_zero_of_collapse
    (L : WeightedLens α W) (x : α) (h : Lens.CollapseToBottom L.lens x) :
    weightedClaim L x = 0 := by
  classical
  dsimp [weightedClaim]
  exact if_neg h

@[simp] theorem weightedCollapse_eq_weight_of_collapse
    (L : WeightedLens α W) (x : α) (h : Lens.CollapseToBottom L.lens x) :
    weightedCollapse L x = L.weight x := by
  classical
  dsimp [weightedCollapse]
  exact if_pos h

@[simp] theorem weightedCollapse_eq_zero_of_satisfiable
    (L : WeightedLens α W) (x : α) (h : Lens.LocallySatisfiable L.lens x) :
    weightedCollapse L x = 0 := by
  classical
  have hc : ¬ Lens.CollapseToBottom L.lens x := fun hcol => hcol h
  dsimp [weightedCollapse]
  exact if_neg hc

end WeightedLens

/-- Semiring-general weighted transport between lens carriers. -/
structure WeightedLensFunctor
    (W : Type v) (V : Type w) [Semiring W] [Semiring V]
    (α : Type u) (β : Type u) where
  mapObj : α → β
  mapWeight : W →+* V

namespace WeightedLensFunctor

variable {W : Type v} {V : Type w} [Semiring W] [Semiring V]
variable {α : Type u} {β : Type u}

/-- Transport a source weighted observation through the weighted functor. -/
def transportWeight (F : WeightedLensFunctor W V α β)
    (L : WeightedLens α W) (x : α) : V :=
  F.mapWeight (L.weight x)

@[simp] theorem transportWeight_zero
    (F : WeightedLensFunctor W V α β)
    (L : WeightedLens α W) (x : α)
    (hx : L.weight x = 0) :
    transportWeight F L x = 0 := by
  simp [transportWeight, hx]

end WeightedLensFunctor

/-- Probability-oriented specialization over `ℝ` with explicit bounds. -/
structure ProbabilisticWeightedLens (α : Type u) where
  base : WeightedLens α ℝ
  bounded : ∀ x : α, 0 ≤ base.weight x ∧ base.weight x ≤ 1

namespace ProbabilisticWeightedLens

variable {α : Type u}

/-- If locally satisfiable, weighted claim is bounded in `[0,1]`. -/
theorem weightedClaim_bounds_of_satisfiable
    (L : ProbabilisticWeightedLens α) (x : α)
    (h : Lens.LocallySatisfiable L.base.lens x) :
    0 ≤ WeightedLens.weightedClaim L.base x ∧
      WeightedLens.weightedClaim L.base x ≤ 1 := by
  have hb := L.bounded x
  constructor
  · simpa [WeightedLens.weightedClaim, h] using hb.1
  · simpa [WeightedLens.weightedClaim, h] using hb.2

/-- If locally collapsed, weighted claim is exactly zero. -/
theorem weightedClaim_eq_zero_of_collapse
    (L : ProbabilisticWeightedLens α) (x : α)
    (h : Lens.CollapseToBottom L.base.lens x) :
    WeightedLens.weightedClaim L.base x = 0 :=
  WeightedLens.weightedClaim_eq_zero_of_collapse L.base x h

end ProbabilisticWeightedLens

end Enrichment
end PerspectivalPlenum
end HeytingLean
