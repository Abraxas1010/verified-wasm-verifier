import HeytingLean.Genesis.EigenformSoup.ObservationGap

/-!
# Genesis.EigenformSoup.ObservationGapCurvature

Finite proxy bridge between observation-gap status and curvature sign.
-/

namespace HeytingLean.Genesis.EigenformSoup

inductive CurvatureSign
  | negative
  | zero
  | positive
deriving DecidableEq, Repr

inductive GapStatus
  | open
  | closed
deriving DecidableEq, Repr

/-- Gap status from numeric observation-gap proxy. -/
def gapStatusNat (expected observed : Nat) : GapStatus :=
  if observationGapNat expected observed = 0 then .closed else .open

/-- Minimal curvature-sign proxy induced from gap status. -/
def curvatureFromGapStatus : GapStatus → CurvatureSign
  | .closed => .positive
  | .open => .negative

theorem curvature_positive_iff_gap_closed
    (expected observed : Nat) :
    curvatureFromGapStatus (gapStatusNat expected observed) = .positive ↔
      observationGapNat expected observed = 0 := by
  unfold gapStatusNat curvatureFromGapStatus
  by_cases hgap : observationGapNat expected observed = 0
  · simp [hgap]
  · simp [hgap]

theorem curvature_negative_iff_gap_open
    (expected observed : Nat) :
    curvatureFromGapStatus (gapStatusNat expected observed) = .negative ↔
      observationGapNat expected observed ≠ 0 := by
  unfold gapStatusNat curvatureFromGapStatus
  by_cases hgap : observationGapNat expected observed = 0
  · simp [hgap]
  · simp [hgap]

/--
Assumption-framed bridge theorem: if a curvature observer reports the same sign
logic as `curvatureFromGapStatus`, then positive/negative sign corresponds
exactly to closed/open gap in the proxy model.
-/
theorem curvature_gap_bridge
    (κ : Nat → Nat → CurvatureSign)
    (hκ : ∀ expected observed,
      κ expected observed = curvatureFromGapStatus (gapStatusNat expected observed))
    (expected observed : Nat) :
    (κ expected observed = .positive ↔ observationGapNat expected observed = 0) ∧
    (κ expected observed = .negative ↔ observationGapNat expected observed ≠ 0) := by
  constructor
  · calc
      κ expected observed = .positive
          ↔ curvatureFromGapStatus (gapStatusNat expected observed) = .positive := by
              simp [hκ]
      _ ↔ observationGapNat expected observed = 0 :=
        curvature_positive_iff_gap_closed expected observed
  · calc
      κ expected observed = .negative
          ↔ curvatureFromGapStatus (gapStatusNat expected observed) = .negative := by
              simp [hκ]
      _ ↔ observationGapNat expected observed ≠ 0 :=
        curvature_negative_iff_gap_open expected observed

end HeytingLean.Genesis.EigenformSoup
