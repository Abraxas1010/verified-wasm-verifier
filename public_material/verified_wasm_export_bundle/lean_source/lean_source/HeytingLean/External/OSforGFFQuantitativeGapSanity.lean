import HeytingLean.External.OSforGFFQuantitativeGap

namespace HeytingLean.External.OSforGFFQuantitativeGapSanity

open HeytingLean.External.OSforGFFQuantitativeGap

variable (m : ℝ) [Fact (0 < m)]

#check HeytingLean.External.OSforGFFQuantitativeGap.massGapDecayConstant
#check HeytingLean.External.OSforGFFQuantitativeGap.QuantitativeContinuumMassGap
#check HeytingLean.External.OSforGFFQuantitativeGap.freeCovariance_exponential_decay
#check HeytingLean.External.OSforGFFQuantitativeGap.freeCovarianceKernel_exponential_decay

example :
    HeytingLean.External.OSforGFFQuantitativeGap.QuantitativeContinuumMassGap m :=
  HeytingLean.External.OSforGFFQuantitativeGap.gaussianFreeField_quantitativeContinuumMassGap m

example :
    HeytingLean.External.OSforGFFBridge.OS4_Clustering
        (HeytingLean.External.OSforGFFBridge.GaussianFreeFieldMeasure m) :=
  (gaussianFreeField_OS4_with_quantitativeContinuumMassGap m).1

end HeytingLean.External.OSforGFFQuantitativeGapSanity
