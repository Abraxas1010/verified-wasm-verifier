import HeytingLean.Genesis.YWitness.Foundations
import HeytingLean.LoF.MRSystems.YBridge
import HeytingLean.LoF.ICC.ConservativeEmbedding

namespace HeytingLean.Computation.YWitness

open HeytingLean.LoF

/-- A productive SKY sequence formed by iteratively wrapping a seed with `Y`. -/
def yProductiveSequence (seed : Comb) : Nat -> Comb
  | 0 => seed
  | n + 1 => Comb.app .Y (yProductiveSequence seed n)

@[simp] theorem yProductiveSequence_zero (seed : Comb) :
    yProductiveSequence seed 0 = seed := rfl

@[simp] theorem yProductiveSequence_succ (seed : Comb) (n : Nat) :
    yProductiveSequence seed (n + 1) = Comb.app .Y (yProductiveSequence seed n) := rfl

/-- A live seed is not already the next `Y`-unfolding of itself. -/
def LiveSeed (seed : Comb) : Prop :=
  seed ≠ Comb.app .Y seed

theorem liveSeed_any (seed : Comb) : LiveSeed seed := by
  intro h
  cases h

theorem yProductiveSequence_step (seed : Comb) (n : Nat) :
    Comb.Step (yProductiveSequence seed (n + 1))
      (Comb.app (yProductiveSequence seed n) (yProductiveSequence seed (n + 1))) := by
  simpa [yProductiveSequence] using Comb.Step.Y_rule (yProductiveSequence seed n)

theorem yProductiveSequence_fixed_shape (seed : Comb) (n : Nat) :
    Comb.IsStepFixedPt (yProductiveSequence seed n) (yProductiveSequence seed (n + 1)) := by
  simpa [Comb.IsStepFixedPt, yProductiveSequence] using Comb.Step.Y_rule (yProductiveSequence seed n)

theorem yProductiveSequence_not_constant_for_live_seed (seed : Comb)
    (hseed : LiveSeed seed) :
    yProductiveSequence seed 0 ≠ yProductiveSequence seed 1 := by
  simpa [LiveSeed, yProductiveSequence] using hseed

/-- The ICC bridge preserves every productive SKY term exactly. -/
@[simp] theorem eraseLegacy_embed_yProductiveSequence (seed : Comb) (n : Nat) :
    ICC.eraseLegacy? (ICC.embedLegacy (yProductiveSequence seed n)) =
      some (yProductiveSequence seed n) := by
  simp

/-- Productive SKY terms stay in the closed ICC image. -/
@[simp] theorem closed_embedLegacy_yProductiveSequence (seed : Comb) (n : Nat) :
    ICC.Term.Closed (ICC.embedLegacy (yProductiveSequence seed n)) := by
  simp

end HeytingLean.Computation.YWitness
