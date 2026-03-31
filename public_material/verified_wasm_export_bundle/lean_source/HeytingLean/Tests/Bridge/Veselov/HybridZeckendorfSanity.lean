import HeytingLean.Bridge.Veselov.HybridZeckendorf

/-!
# Hybrid Zeckendorf Sanity
-/

namespace HeytingLean.Tests.Bridge.Veselov

open HeytingLean.Bridge.Veselov.HybridZeckendorf

#check weight
#check weight_closed
#check fib_double_identity
#check HybridNumber
#check LazyHybridNumber
#check eval
#check lazyEval
#check normalize
#check add
#check multiplyBinary
#check anchor_invariant_euler_reentry
#check transport_coherence_baseStabilizes_split
#check zeckendorf_unique
#check canonical_eval_injective
#check add_comm_repr
#check supportCard_single_level_bound
#check active_levels_bound
#check density_upper_bound
#check carryAt_idempotent
#check carryAt_monotone
#check normalize_is_closure_operator

example : weight 0 = 1 := by decide
example : weight 1 = 1000 := by decide
example : 0 < weight 4 := weight_pos 4

example : eval (fromNat 0) = 0 := eval_fromNat 0
example : eval (fromNat 123456789) = 123456789 := eval_fromNat 123456789

example : eval (add (fromNat 789) (fromNat 456)) = 1245 := by
  norm_num [add_fromNat]

example : eval (multiplyBinary (fromNat 12) (fromNat 34)) = 408 := by
  norm_num [multiplyBinary_correct]

example : eval (normalize (fromNat 99999)) = 99999 := by
  calc
    eval (normalize (fromNat 99999)) = lazyEval (fromNat 99999) := normalize_sound (fromNat 99999)
    _ = 99999 := lazyEval_fromNat 99999

end HeytingLean.Tests.Bridge.Veselov
