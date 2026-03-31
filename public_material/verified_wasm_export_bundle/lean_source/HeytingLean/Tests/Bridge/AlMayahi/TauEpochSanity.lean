import HeytingLean.Bridge.AlMayahi.TauEpoch

/-!
# TauEpoch Sanity
-/

namespace HeytingLean.Tests.Bridge.AlMayahi

open HeytingLean.Bridge.AlMayahi.TauEpoch

#check wtMean
#check chi2Wt
#check birge
#check lambdaStat
#check ProjectionOperator
#check TauProxyAssignment
#check ValidTauProxy
#check TwoClockModel
#check Prediction
#check two_clock_necessity

example : (defaultTauProxy .cosmology).domain = .cosmology := rfl
example : ValidTauProxy (defaultTauProxy .particlePhysics) := defaultTauProxy_valid _

example : h0Ensemble.size = 7 := rfl
example : lhcKappaTable.size = 7 := rfl
example : nmrTable.size = 8 := rfl
example : neutronTable.size = 9 := rfl
example : protonTable.size = 6 := rfl
example : muonTable.size = 3 := rfl

example : predictionStatusCounts = (3, 3, 0, 0) := by native_decide

#eval alphaBridgeRatioFloat
#eval ("tau-epoch prediction counts", predictionStatusCounts)

end HeytingLean.Tests.Bridge.AlMayahi
