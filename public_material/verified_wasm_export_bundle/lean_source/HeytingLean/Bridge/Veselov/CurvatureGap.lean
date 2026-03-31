import Mathlib.Data.Int.Basic

/-!
# Bridge.Veselov.CurvatureGap

Constructive P3 bridge surface:
- curvature-sign to observation-gap classifier,
- regular-model packaging with explicit implication contracts.
-/

namespace HeytingLean.Bridge.Veselov

/-- Observation-gap status induced by a curvature sign. -/
inductive GapStatus
  | open
  | critical
  | closed
  deriving DecidableEq, Repr

/-- Sign classifier used by the curvature-gap bridge. -/
def statusOfCurvature (κ : Int) : GapStatus :=
  if 0 < κ then GapStatus.open
  else if κ = 0 then GapStatus.critical
  else GapStatus.closed

theorem status_open_of_pos {κ : Int} (h : 0 < κ) :
    statusOfCurvature κ = GapStatus.open := by
  simp [statusOfCurvature, h]

theorem status_critical_of_zero {κ : Int} (h : κ = 0) :
    statusOfCurvature κ = GapStatus.critical := by
  subst h
  simp [statusOfCurvature]

theorem status_closed_of_nonpos_nonzero {κ : Int}
    (hnot : ¬ 0 < κ) (h0 : κ ≠ 0) :
    statusOfCurvature κ = GapStatus.closed := by
  simp [statusOfCurvature, hnot, h0]

/-- Closed-form regular-model carrier for curvature-gap statements. -/
structure RegularCurvatureModel where
  curvature : Int

/-- Gap status extracted from a regular-model curvature parameter. -/
def modelGapStatus (M : RegularCurvatureModel) : GapStatus :=
  statusOfCurvature M.curvature

/-- P3 packaged theorem: curvature sign controls gap status. -/
theorem model_curvature_gap_correspondence (M : RegularCurvatureModel) :
    (0 < M.curvature → modelGapStatus M = GapStatus.open) ∧
    (M.curvature = 0 → modelGapStatus M = GapStatus.critical) ∧
    ((¬ 0 < M.curvature) ∧ M.curvature ≠ 0 → modelGapStatus M = GapStatus.closed) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simpa [modelGapStatus] using status_open_of_pos h
  · intro h
    simpa [modelGapStatus] using status_critical_of_zero h
  · intro h
    rcases h with ⟨hnot, h0⟩
    simpa [modelGapStatus] using status_closed_of_nonpos_nonzero hnot h0

/--
Restricted P3 carrier for finite regular graph classes.
This keeps the theorem scope explicit while reusing the curvature-sign classifier.
-/
structure FiniteRegularCurvatureModel where
  vertexCount : Nat
  degree : Nat
  degree_le_vertexCount : degree ≤ vertexCount
  curvature : Int

/-- Gap status extracted from the restricted finite-regular model. -/
def finiteRegularGapStatus (M : FiniteRegularCurvatureModel) : GapStatus :=
  statusOfCurvature M.curvature

/--
Restricted finite-regular P3 theorem:
within this scoped carrier, curvature sign determines gap status.
-/
theorem restricted_finite_regular_curvature_gap (M : FiniteRegularCurvatureModel) :
    (0 < M.curvature → finiteRegularGapStatus M = GapStatus.open) ∧
    (M.curvature = 0 → finiteRegularGapStatus M = GapStatus.critical) ∧
    ((¬ 0 < M.curvature) ∧ M.curvature ≠ 0 → finiteRegularGapStatus M = GapStatus.closed) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simpa [finiteRegularGapStatus] using status_open_of_pos h
  · intro h
    simpa [finiteRegularGapStatus] using status_critical_of_zero h
  · intro h
    rcases h with ⟨hnot, h0⟩
    simpa [finiteRegularGapStatus] using status_closed_of_nonpos_nonzero hnot h0

end HeytingLean.Bridge.Veselov
