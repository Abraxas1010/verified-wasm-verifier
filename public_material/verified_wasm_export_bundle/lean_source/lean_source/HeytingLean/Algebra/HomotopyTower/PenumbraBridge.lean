import HeytingLean.Algebra.HomotopyTower.Stabilization
import HeytingLean.Bridges.Nucleus.Conversions
import HeytingLean.Generative.WolframBridge.FixedPointPredicate
import HeytingLean.HossenfelderNoGo.HeytingBoundary.GapNonZero

namespace HeytingLean
namespace Algebra
namespace HomotopyTower

open HeytingLean.Bridges
open HeytingLean.Generative.WolframBridge
open HeytingLean.HossenfelderNoGo.HeytingBoundary

universe u

variable {α : Type u} [Order.Frame α]

/-- View the stabilized limit nucleus through the existing boundary-no-go interface. -/
noncomputable def stableBoundaryNucleus (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    BoundaryNucleus α :=
  Nucleus.mathlibToCore (limitNucleus T hfin)

/-- The stable boundary nucleus lands exactly in the fixed-point predicate bridge. -/
theorem stableBoundaryNucleus_isBoolean_iff_invariant
    (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    isBoolean (stableBoundaryNucleus T hfin) ↔
      NucleusInvariant (stableBoundaryNucleus T hfin) :=
  hossenfelder_isBoolean_iff_nucleusInvariant (stableBoundaryNucleus T hfin)

/-- A moved point in the stabilized boundary yields a nonempty Hossenfelder gap. -/
theorem stableBoundaryGap_nonempty_of_moved
    (T : NucleusTower (α := α)) (hfin : FiniteImage T) (a : α)
    (ha : a ∈ stableBoundary T hfin) :
    boundaryGap (stableBoundaryNucleus T hfin) a ≠ ∅ := by
  apply boundaryGap_nonempty_of_moved
  simpa [stableBoundaryNucleus, stableBoundary, boundary, limitNucleus, Nucleus.mathlibToCore] using ha

/-- A fixed point at the stabilized boundary has empty Hossenfelder gap. -/
theorem stableBoundaryGap_eq_empty_of_fixed
    (T : NucleusTower (α := α)) (hfin : FiniteImage T) (a : α)
    (ha : a ∉ stableBoundary T hfin) :
    boundaryGap (stableBoundaryNucleus T hfin) a = ∅ := by
  apply boundaryGap_eq_empty_of_fixed
  by_contra hmoved
  exact ha <| by
    simpa [stableBoundaryNucleus, stableBoundary, boundary, limitNucleus, Nucleus.mathlibToCore] using hmoved

/-- Under the existing Boolean-boundary bridge, the stabilized boundary nucleus is non-Boolean. -/
theorem stableBoundary_not_boolean_of_bridge
    (T : NucleusTower (α := α)) (hfin : FiniteImage T)
    (hBridge : BooleanBoundaryBridge (stableBoundaryNucleus T hfin)) :
    ¬ isBoolean (stableBoundaryNucleus T hfin) :=
  boundary_necessarily_non_boolean (stableBoundaryNucleus T hfin) hBridge

/-- The existing Hossenfelder bridge gives a nonempty stabilized boundary gap witness. -/
theorem stableBoundary_has_gap_of_bridge
    (T : NucleusTower (α := α)) (hfin : FiniteImage T)
    (hBridge : BooleanBoundaryBridge (stableBoundaryNucleus T hfin)) :
    ∃ a : α, boundaryGap (stableBoundaryNucleus T hfin) a ≠ ∅ :=
  gap_nonzero_at_boundary (stableBoundaryNucleus T hfin) hBridge

/-- The bridge also yields a genuinely moved point of the stabilized limit nucleus. -/
theorem stableBoundary_has_moved_point_of_bridge
    (T : NucleusTower (α := α)) (hfin : FiniteImage T)
    (hBridge : BooleanBoundaryBridge (stableBoundaryNucleus T hfin)) :
    ∃ a : α, a ∈ stableBoundary T hfin := by
  obtain ⟨a, ha⟩ := boundary_has_nontrivial_fixed_points (stableBoundaryNucleus T hfin) hBridge
  refine ⟨a, ?_⟩
  simpa [stableBoundaryNucleus, stableBoundary, boundary, Core.Nucleus.fixedPoints,
    limitNucleus, Nucleus.mathlibToCore] using ha

end HomotopyTower
end Algebra
end HeytingLean
