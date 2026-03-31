import HeytingLean.Util.Iterate

namespace HeytingLean
namespace Computation

open HeytingLean.Util

/-- Bounded stabilization: within `k` steps there exists an iterate
    that is a fixed point of `f`. -/
def stabilizes (k : Nat) (f : α → α) (a : α) : Prop :=
  ∃ n ≤ k, f (iterateN n f a) = iterateN n f a

/-- A stabilized iterate yields a fixed point (existential witness). -/
lemma stabilizes_implies_exists_fixed {k : Nat} {f : α → α} {a : α} :
    stabilizes k f a → ∃ out, f out = out := by
  intro h
  rcases h with ⟨n, _hle, hfix⟩
  refine ⟨iterateN n f a, ?_⟩
  simpa using hfix

end Computation
end HeytingLean

