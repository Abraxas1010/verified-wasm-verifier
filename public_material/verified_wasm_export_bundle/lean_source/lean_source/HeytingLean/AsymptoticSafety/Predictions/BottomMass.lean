import HeytingLean.AsymptoticSafety.GravityMatter

namespace HeytingLean
namespace AsymptoticSafety

theorem topBottomRatio_from_shift_bound (model : GravityMatterModel)
    {calibrationBound driftBound : ℝ}
    (hcal : |model.ratioCalibration| ≤ calibrationBound)
    (hdrift :
      |effectiveTopYukawaShift model - effectiveBottomYukawaShift model| ≤ driftBound)
    (hbudget :
      calibrationBound * driftBound ≤ model.targets.topBottomRatio.tolerance) :
    model.targets.topBottomRatio.Contains (predictTopBottomRatio model) := by
  have hcal_nonneg : 0 ≤ calibrationBound := le_trans (abs_nonneg _) hcal
  have hmul1 :
      |model.ratioCalibration| *
          |effectiveTopYukawaShift model - effectiveBottomYukawaShift model| ≤
        calibrationBound *
          |effectiveTopYukawaShift model - effectiveBottomYukawaShift model| := by
    exact mul_le_mul_of_nonneg_right hcal (abs_nonneg _)
  have hmul2 :
      calibrationBound *
          |effectiveTopYukawaShift model - effectiveBottomYukawaShift model| ≤
        calibrationBound * driftBound := by
    exact mul_le_mul_of_nonneg_left hdrift hcal_nonneg
  rw [ExperimentalBand.Contains, topBottomRatio_abs_error_eq_rg_drift]
  exact le_trans (le_trans hmul1 hmul2) hbudget

end AsymptoticSafety
end HeytingLean
