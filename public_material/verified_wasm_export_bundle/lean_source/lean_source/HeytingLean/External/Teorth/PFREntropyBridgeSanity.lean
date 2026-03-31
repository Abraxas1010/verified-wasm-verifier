import HeytingLean.External.Teorth.PFREntropyBridge

namespace HeytingLean.External.Teorth.PFREntropyBridgeSanity

open MeasureTheory ProbabilityTheory
open HeytingLean.External.Teorth.PFREntropyBridge

#check chain_rule
#check entropy_comap
#check entropy_pair_eq_add
#check mutualInfo_eq

section
variable {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
variable (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)

noncomputable def entropyAlias : ℝ := HeytingLean.External.Teorth.PFREntropyBridge.entropy X μ
noncomputable def condEntropyAlias : ℝ := HeytingLean.External.Teorth.PFREntropyBridge.condEntropy X Y μ
noncomputable def mutualInfoAlias : ℝ := HeytingLean.External.Teorth.PFREntropyBridge.mutualInfo X Y μ

example : HeytingLean.External.Teorth.PFREntropyBridge.entropy X μ = ProbabilityTheory.entropy X μ := rfl
example : HeytingLean.External.Teorth.PFREntropyBridge.condEntropy X Y μ = ProbabilityTheory.condEntropy X Y μ := rfl
example : HeytingLean.External.Teorth.PFREntropyBridge.mutualInfo X Y μ = ProbabilityTheory.mutualInfo X Y μ := rfl

end

end HeytingLean.External.Teorth.PFREntropyBridgeSanity
