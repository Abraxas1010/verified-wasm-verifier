import HeytingLean.External.Teorth.AnalysisProbabilityBridge

namespace HeytingLean.External.Teorth.AnalysisProbabilityBridgeSanity

open MeasureTheory ProbabilityTheory
open HeytingLean.External.Teorth.AnalysisProbabilityBridge

#check prob
#check prob_nonneg
#check prob_top
#check prob_disj_sup
#check tsum_of_tsum
#check upward_continuous
#check indicator'
#check indicator'_of_mem
#check indicator'_of_notMem

section
variable {A : Type*} [BooleanAlgebra A]
variable (P : HeytingLean.External.Teorth.AnalysisProbabilityBridge.FinitelyAdditive A) (s : A)

example : finiteProb P s = P.prob s := rfl

end

end HeytingLean.External.Teorth.AnalysisProbabilityBridgeSanity
