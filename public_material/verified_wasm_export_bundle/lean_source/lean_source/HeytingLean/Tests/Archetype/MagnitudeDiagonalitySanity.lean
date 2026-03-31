import HeytingLean.Metrics.Magnitude.Diagonality

namespace HeytingLean
namespace Tests
namespace Archetype

open Metrics.Magnitude

private instance boolUnitMetricSpaceDiag : MetricMagnitudeSpace Bool where
  toFintype := inferInstance
  decEq := inferInstance
  dist := fun x y => if x = y then 0 else 1
  dist_self := by
    intro x
    simp
  dist_symm := by
    intro x y
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy, eq_comm]

theorem bool_unitEdge : UnitEdgeMetric (α := Bool) := by
  intro x y hxy
  simp [MetricMagnitudeSpace.dist, hxy]

example : IsDiagonal (α := Bool) := by
  exact unitEdge_implies_diagonal bool_unitEdge

example : IsChainDiagonal (α := Bool) := by
  exact unitEdge_implies_chainDiagonal bool_unitEdge

example : IsDiagonal (α := Bool) := by
  have hdiag : IsDiagonal (α := Bool) := unitEdge_implies_diagonal bool_unitEdge
  exact diagonal_retract (α := Bool) (β := Bool) (r := id) (s := id)
    (by intro y; rfl)
    (by intro x y; rfl)
    hdiag

end Archetype
end Tests
end HeytingLean
