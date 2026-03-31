import Mathlib
import HeytingLean.AsymptoticSafety

namespace HeytingLean
namespace Tests
namespace AsymptoticSafety

open HeytingLean.AsymptoticSafety

def testTruncation : TruncationScheme where
  newtonStar := 1
  cosmologicalStar := 0
  gravitonEta := -2
  yukawaGravityShift := 1
  quarticGravityShift := 1
  portalGravityShift := 0
  signature := "Euclidean"
  source := "test"

def testProfile : CriticalExponentProfile where
  G_Newton := 2
  cosmological := 1
  topYukawa := -1
  bottomYukawa := -2
  higgsQuartic := -2
  gaugeU1 := -1
  gaugeSU2 := -1
  gaugeSU3 := -1
  portalCoupling := -1
  source := "test"

def testTargets : ExperimentalTargets where
  topMass := ⟨10, 2⟩
  higgsMass := ⟨12, 5⟩
  topBottomRatio := ⟨4, 5⟩
  neutrinoMassUpper := 1
  source := "test"

def demoSystem : BetaSystem where
  truncation := testTruncation
  critical := testProfile

def demoMatter : MatterSector where
  content := ⟨3, 1, 1⟩
  yukawaLift := 1
  quarticLift := 2
  portalLift := 0
  source := "sanity"

noncomputable def demoModel : GravityMatterModel where
  system := demoSystem
  matter := demoMatter
  targets := testTargets
  topCalibration := 1
  higgsCalibration := -2
  ratioCalibration := 3
  neutrinoCalibration := 1 / 10
  source := "sanity"

example : linearizedBeta demoSystem (gravitationalFixedPoint demoSystem.truncation) = 0 :=
  linearizedBeta_at_fixedPoint demoSystem

example (g : CouplingPoint) :
    projectToUVSafe demoSystem (projectToUVSafe demoSystem g) = projectToUVSafe demoSystem g :=
  projectToUVSafe_idempotent demoSystem g

example : gaussianMatterCompatible (gravitationalFixedPoint eichhornBenchmark) :=
  gravitationalFixedPoint_gaussianMatterCompatible eichhornBenchmark

example : 0 < matterBackreaction demoMatter := by
  apply matter_matters
  · change 0 < (3 : Nat)
    norm_num
  · norm_num [demoMatter]
  · norm_num [demoMatter]
  · norm_num [demoMatter]

example : demoModel.targets.topMass.Contains (predictTopMass demoModel) := by
  refine topMass_from_shift_bound (model := demoModel)
      (calibrationBound := 1) (driftBound := 1) ?_ ?_ ?_
  · norm_num [demoModel]
  · norm_num [demoModel, demoSystem, demoMatter, testProfile, testTruncation,
      effectiveTopYukawaShift, gravitationalTopDrift]
  · norm_num [demoModel, testTargets]

example : demoModel.targets.higgsMass.Contains (predictHiggsMass demoModel) := by
  refine higgsMass_from_shift_bound (model := demoModel)
      (calibrationBound := 2) (driftBound := 1) ?_ ?_ ?_
  · norm_num [demoModel]
  · norm_num [demoModel, demoSystem, demoMatter, testProfile, testTruncation, demoMatter,
      effectiveHiggsQuarticShift, gravitationalQuarticDrift]
  · norm_num [demoModel, testTargets]

example : demoModel.targets.topBottomRatio.Contains (predictTopBottomRatio demoModel) := by
  refine topBottomRatio_from_shift_bound (model := demoModel)
      (calibrationBound := 3) (driftBound := 1) ?_ ?_ ?_
  · norm_num [demoModel]
  · norm_num [demoModel, demoSystem, demoMatter, testProfile, testTruncation,
      effectiveTopYukawaShift, effectiveBottomYukawaShift, gravitationalTopDrift,
      gravitationalBottomDrift]
  · norm_num [demoModel, testTargets]

example : predictNeutrinoUpper demoModel ≤ demoModel.targets.neutrinoMassUpper := by
  have hpos : 0 < matterBackreaction demoMatter := by
    apply matter_matters
    · change 0 < (3 : Nat)
      norm_num
    · norm_num [demoMatter]
    · norm_num [demoMatter]
    · norm_num [demoMatter]
  have hback : 0 ≤ matterBackreaction demoMatter := by
    exact le_of_lt hpos
  refine neutrinoMass_below_target (model := demoModel)
      (calibrationBound := 1 / 10) (backreactionBound := 5) ?_ ?_ ?_ ?_
  · exact hback
  · norm_num [demoModel]
  · norm_num [demoModel, demoMatter, matterBackreaction]
  · norm_num [demoModel, demoSystem, demoMatter, testProfile, testTruncation, testTargets,
      neutrinoDamping, gravitationalTopDrift]

example : uvSafeSet demoSystem ⊆ carrier (portalExclusionRegion demoSystem) :=
  no_simplest_WIMP demoSystem (by
    dsimp [PortalScreeningHypothesis, demoSystem, testTruncation, testProfile]
    norm_num)

def demoTensor : TensorFieldTheory.TensorTruncation where
  orderN := 3
  screening := 1
  antiscreening := 1
  quarticFixedPoint := 1
  source := "sanity"

example : TensorFieldTheory.balanced demoTensor := by
  simp [TensorFieldTheory.balanced, TensorFieldTheory.screeningBalance, demoTensor]

example : TensorFieldTheory.nonGaussianFixedPoint demoTensor := by
  exact TensorFieldTheory.balanced_nonGaussian_fixedPoint demoTensor (by
    simp [TensorFieldTheory.balanced, TensorFieldTheory.screeningBalance, demoTensor]) (by
    norm_num [demoTensor])

def scaleSensitivePoint : CouplingPoint where
  G_Newton := 3
  cosmological := 0
  topYukawa := 0
  bottomYukawa := 0
  higgsQuartic := 0
  gaugeU1 := 0
  gaugeSU2 := 0
  gaugeSU3 := 0
  portalCoupling := 0

example : scaleSensitivePoint ∉ scaleSafeSet demoSystem uvScale := by
  simp [scaleSafeSet, scaleThreshold, scaleSensitivePoint, uvScale, demoSystem, testProfile,
    testTruncation, gravitationalFixedPoint]

example : scaleSensitivePoint ∈ scaleSafeSet demoSystem ⟨3, 0⟩ := by
  simp [scaleSafeSet, scaleThreshold, scaleSensitivePoint, demoSystem, testProfile,
    testTruncation, gravitationalFixedPoint]
  have hlt : (2 : ℝ) < 3 := by linarith
  simpa using hlt

example : Renormalization.logicAtScale uvScale = .constructive :=
  constructive_at_uv

example : freeEnergyProxy demoSystem (gravitationalFixedPoint demoSystem.truncation) = 0 :=
  freeEnergy_at_fixedPoint_zero demoSystem

example (g : CouplingPoint) : (Extraction.certifyProjectionRun demoSystem g).steps = 1 :=
  Extraction.certificate_has_single_step demoSystem g

example (g : CouplingPoint) :
    isUVSafe demoSystem (Extraction.certifyProjectionRun demoSystem g).final :=
  Extraction.certificate_safe_final demoSystem g

#eval Extraction.demoRK4.portalCoupling

end AsymptoticSafety
end Tests
end HeytingLean
