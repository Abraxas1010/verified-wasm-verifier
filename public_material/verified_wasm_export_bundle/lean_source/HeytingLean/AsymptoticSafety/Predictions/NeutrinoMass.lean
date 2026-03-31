import HeytingLean.AsymptoticSafety.GravityMatter

namespace HeytingLean
namespace AsymptoticSafety

theorem neutrinoMass_below_target (model : GravityMatterModel)
    (hback : 0 ≤ matterBackreaction model.matter)
    {calibrationBound backreactionBound : ℝ}
    (hcal : |model.neutrinoCalibration| ≤ calibrationBound)
    (hreact : matterBackreaction model.matter ≤ backreactionBound)
    (hbudget :
      calibrationBound * backreactionBound ≤
        model.targets.neutrinoMassUpper * neutrinoDamping model) :
    predictNeutrinoUpper model ≤ model.targets.neutrinoMassUpper := by
  have hdamp : 0 < neutrinoDamping model := neutrinoDamping_pos model
  have habs :
      |matterBackreaction model.matter| = matterBackreaction model.matter :=
    abs_of_nonneg hback
  have hcal_nonneg : 0 ≤ calibrationBound := le_trans (abs_nonneg _) hcal
  have hreact_nonneg : 0 ≤ backreactionBound := le_trans hback hreact
  have hreactAbs : |matterBackreaction model.matter| ≤ backreactionBound := by
    simpa [habs] using hreact
  have hmul1 :
      |model.neutrinoCalibration| * |matterBackreaction model.matter| ≤
        calibrationBound * |matterBackreaction model.matter| := by
    exact mul_le_mul_of_nonneg_right hcal (abs_nonneg _)
  have hmul2 :
      calibrationBound * |matterBackreaction model.matter| ≤
        calibrationBound * backreactionBound := by
    exact mul_le_mul_of_nonneg_left hreactAbs hcal_nonneg
  rw [predictNeutrinoUpper]
  refine (div_le_iff₀ hdamp).2 ?_
  calc
    neutrinoNumerator model = |model.neutrinoCalibration| * |matterBackreaction model.matter| := rfl
    _ ≤ calibrationBound * backreactionBound := le_trans hmul1 hmul2
    _ ≤ model.targets.neutrinoMassUpper * neutrinoDamping model := hbudget

end AsymptoticSafety
end HeytingLean
