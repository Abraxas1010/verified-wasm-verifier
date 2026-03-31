import HeytingLean.External.Teorth.AnalysisStable
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Teorth Analysis Probability Bridge

Stable import surface for measure/probability declarations from the `teorth/analysis` corpus,
with aliases intended for reuse from HeytingLean domains (probability, crypto, physics).
-/

namespace HeytingLean.External.Teorth.AnalysisProbabilityBridge

open MeasureTheory ProbabilityTheory

abbrev FinitelyAdditive (A : Type*) [BooleanAlgebra A] := ProbabilityTheory.FinitelyAdditive A

def finiteProb {A : Type*} [BooleanAlgebra A] (P : FinitelyAdditive A) (s : A) : ℝ := P.prob s

export ProbabilityTheory.FinitelyAdditive (prob prob_nonneg prob_top prob_disj_sup)
export ENNReal (tsum_of_tsum upward_continuous)
export Set (indicator' indicator'_of_mem indicator'_of_notMem)

#check ProbabilityTheory.Kernel
#check ProbabilityMeasure
#check ProbabilityTheory.FinitelyAdditive
#check ProbabilityTheory.FinitelyAdditive.prob_nonneg
#check ProbabilityTheory.FinitelyAdditive.prob_top
#check ProbabilityTheory.FinitelyAdditive.prob_disj_sup
#check ENNReal.tsum_of_tsum
#check ENNReal.upward_continuous
#check Set.indicator'
#check Set.indicator'_of_mem
#check Set.indicator'_of_notMem

end HeytingLean.External.Teorth.AnalysisProbabilityBridge
