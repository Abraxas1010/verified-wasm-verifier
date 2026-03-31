import HeytingLean.Bridge.Sharma.AetherPruning

namespace HeytingLean.Tests.Bridge.Sharma

open HeytingLean.Bridge.Sharma.AetherPruning

#check @prune_safe
#check @can_prune_sound
#check @hierarchical_prune_safe
#check @upper_bound_tight

example :
    ∃ (q : EuclideanSpace Real (Fin 1)) (B : BlockMeta 1)
      (k : EuclideanSpace Real (Fin 1)),
      q ≠ 0 ∧ B.contains k ∧ inner Real q k = upperBoundScore q B := by
  simpa using (upper_bound_tight (D := 1) (by decide : 0 < (1 : ℕ)))

end HeytingLean.Tests.Bridge.Sharma
