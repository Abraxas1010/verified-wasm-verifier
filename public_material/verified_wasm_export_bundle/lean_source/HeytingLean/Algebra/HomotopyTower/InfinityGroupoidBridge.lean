import HeytingLean.Algebra.HomotopyTower.ComparisonData
import HeytingLean.LoF.Combinators.InfinityGroupoid.SSet

namespace HeytingLean
namespace Algebra
namespace HomotopyTower

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

universe u

variable {α : Type u} [Order.Frame α]

/-- A concrete infinity-groupoid presentation: a carrier with a groupoid structure and Kan nerve. -/
structure InftyGroupoidPresentation where
  Obj : Type u
  instGroupoid : Groupoid Obj
  kan : SSet.KanComplex (@CategoryTheory.nerve Obj instGroupoid.toCategory)

attribute [instance] InftyGroupoidPresentation.instGroupoid

/-- The comparison data determines a concrete infinity-groupoid presentation object. -/
noncomputable def comparisonInftyGroupoidPresentation
    (T : NucleusTower (α := α)) (hfin : FiniteImage T)
    (cmp : StableTransportComparison T hfin) : InftyGroupoidPresentation :=
  let hG : Groupoid (stableGroupoidLimit cmp.Q) := by
    dsimp [stableGroupoidLimit, stableGroupoidTower]
    infer_instance
  { Obj := stableGroupoidLimit cmp.Q
    instGroupoid := hG
    kan := by
      letI : Groupoid (stableGroupoidLimit cmp.Q) := hG
      exact HeytingLean.LoF.Combinators.InfinityGroupoid.exported_groupoid_nerve_kanComplex
        (C := stableGroupoidLimit cmp.Q) }

/-- Final packaging theorem for the currently implemented stronger bridge.

The nontrivial comparison from the fixed-point tower limit to the transport-groupoid limit is still
explicit input data. What is now fully implemented is the stabilized-source equivalence and the
generic Kan-complex theorem for nerves of groupoids.
-/
theorem stabilized_fixed_point_category_has_infty_groupoid_presentation
    (T : NucleusTower (α := α)) (hfin : FiniteImage T)
    (cmp : StableTransportComparison T hfin) :
    Nonempty
      (StableFixedPointCategory T hfin ≌ (comparisonInftyGroupoidPresentation T hfin cmp).Obj) := by
  exact ⟨(stableObjectEquivalence T hfin).trans cmp.limitEquiv⟩

end HomotopyTower
end Algebra
end HeytingLean
