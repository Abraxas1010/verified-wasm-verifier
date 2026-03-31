import HeytingLean.Genesis.YWitness.FullChain

namespace HeytingLean.Tests.YWitness

open HeytingLean.Computation.YWitness
open HeytingLean.LoF

example : yProductiveSequence .K 0 = .K := rfl

example : yProductiveSequence .K 1 = Comb.app .Y .K := rfl

example : yProductiveSequence .K 0 ≠ yProductiveSequence .K 1 := by
  exact yProductiveSequence_not_constant_for_live_seed .K (liveSeed_any .K)

example :
    ∃ ed : Comb.EventData,
      (ed, Comb.app (yProductiveSequence .K 0) (yProductiveSequence .K 1)) ∈
        Comb.stepEdges (yProductiveSequence .K 1) := by
  exact finite_multiway_crystallization .K 0

example :
    0 < normalizedWeightAtDepth 1 .K := by
  exact finite_productive_paths_have_positive_weight 1 .K

example :
    (pathCountAtDepth 1 .K : Rat) * normalizedWeightAtDepth 1 .K = 1 := by
  exact normalizedWeight_total_mass_one 1 .K

end HeytingLean.Tests.YWitness
