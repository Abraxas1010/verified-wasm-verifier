import HeytingLean.External.OSforGFFBridge

namespace HeytingLean.External.OSforGFFBridgeSanity

variable (m : ℝ) [Fact (0 < m)]

example : HeytingLean.External.OSforGFFBridge.SatisfiesAllOS
    (HeytingLean.External.OSforGFFBridge.GaussianFreeFieldMeasure m) :=
  HeytingLean.External.OSforGFFBridge.gaussianFreeField_satisfies_all_OS_axioms m

example : HeytingLean.External.OSforGFFBridge.OS0_Analyticity
    (HeytingLean.External.OSforGFFBridge.GaussianFreeFieldMeasure m) :=
  HeytingLean.External.OSforGFFBridge.gaussianFreeField_satisfies_OS0 m

example : HeytingLean.External.OSforGFFBridge.OS1_Regularity
    (HeytingLean.External.OSforGFFBridge.GaussianFreeFieldMeasure m) :=
  HeytingLean.External.OSforGFFBridge.gaussianFreeField_satisfies_OS1 m

example : HeytingLean.External.OSforGFFBridge.OS2_EuclideanInvariance
    (HeytingLean.External.OSforGFFBridge.GaussianFreeFieldMeasure m) :=
  HeytingLean.External.OSforGFFBridge.gaussianFreeField_satisfies_OS2 m

example : HeytingLean.External.OSforGFFBridge.OS3_ReflectionPositivity
    (HeytingLean.External.OSforGFFBridge.GaussianFreeFieldMeasure m) :=
  HeytingLean.External.OSforGFFBridge.gaussianFreeField_satisfies_OS3 m

example : HeytingLean.External.OSforGFFBridge.OS4_Clustering
    (HeytingLean.External.OSforGFFBridge.GaussianFreeFieldMeasure m) :=
  HeytingLean.External.OSforGFFBridge.gaussianFreeField_satisfies_OS4 m

example : HeytingLean.External.OSforGFFBridge.OS4_Ergodicity
    (HeytingLean.External.OSforGFFBridge.GaussianFreeFieldMeasure m) :=
  HeytingLean.External.OSforGFFBridge.gaussianFreeField_satisfies_OS4_ergodicity m

end HeytingLean.External.OSforGFFBridgeSanity
