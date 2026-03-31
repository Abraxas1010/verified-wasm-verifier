import Mathlib.Analysis.Asymptotics.Defs
import HeytingLean.Epiplexity.Conditional

namespace HeytingLean
namespace Epiplexity

open Filter
open Asymptotics

noncomputable section

/-!
Epiplexity emergence (paper Definition 14).

The paper’s notion is asymptotic in the ambient bitstring size `n`, comparing the conditional
epiplexity gaps between two time bounds `T₁(n) = o(T₂(n))` for a one-step vs multi-step map.

Our core development tracks conditional epiplexity via an explicit optimizer witness
`OptimalCondProg` (paper Definition 11). This file packages the *predicate only*; the paper’s
examples are empirical.
-/

namespace Emergence

open HeytingLean.Probability.InfoTheory

/-- Absolute gap in conditional epiplexity `S_T(Y|X)` between two optimizers (as a natural). -/
def STGap {α β : Type u} [Fintype α] [Fintype β] {T₁ T₂ : Nat} {PXY : FinDist (α × β)}
    (opt₁ : OptimalCondProg (α := α) (β := β) T₁ PXY)
    (opt₂ : OptimalCondProg (α := α) (β := β) T₂ PXY) : Nat :=
  Int.natAbs (Int.ofNat opt₁.ST - Int.ofNat opt₂.ST)

/-- A `Θ(1)`-style condition for a natural sequence: eventually bounded above and below by
positive constants. -/
def IsThetaOne (f : Nat → Nat) : Prop :=
  ∃ c₁ c₂ : Nat, 0 < c₁ ∧ (∀ᶠ n in atTop, c₁ ≤ f n) ∧ (∀ᶠ n in atTop, f n ≤ c₂)

/-- An `ω(1)`-style condition for a natural sequence: tends to infinity. -/
def IsOmegaOne (f : Nat → Nat) : Prop :=
  Tendsto f atTop atTop

/--
`EpiplexityEmergent P` is the emergence predicate of Definition 14, phrased in terms of a
step-indexed family of joint distributions `P n k` over bitstrings of length `n`.

Intuition: `P n 1` models the one-step pair `(X, Φ(X))` while `P n (k n)` models the multistep
pair `(X, Φ^{k(n)}(X))`. The predicate compares the *conditional epiplexity gaps* between two
time bounds `T₁, T₂` with `T₁ = o(T₂)`.
-/
def EpiplexityEmergent (P : ∀ n : Nat, Nat → FinDist (BitStr n × BitStr n)) : Prop :=
  ∃ (T₁ T₂ : Nat → Nat) (k : Nat → Nat),
    (fun n => (T₁ n : ℝ)) =o[atTop] (fun n => (T₂ n : ℝ)) ∧
      (∃ opt₁₁ :
          ∀ n,
            OptimalCondProg (α := BitStr n) (β := BitStr n) (T := T₁ n) (PXY := P n 1),
        ∃ opt₂₁ :
          ∀ n,
            OptimalCondProg (α := BitStr n) (β := BitStr n) (T := T₂ n) (PXY := P n 1),
        ∃ opt₁k :
          ∀ n,
            OptimalCondProg (α := BitStr n) (β := BitStr n) (T := T₁ n) (PXY := P n (k n)),
        ∃ opt₂k :
          ∀ n,
            OptimalCondProg (α := BitStr n) (β := BitStr n) (T := T₂ n) (PXY := P n (k n)),
          IsThetaOne (fun n => STGap (opt₁ := opt₁₁ n) (opt₂ := opt₂₁ n)) ∧
            IsOmegaOne (fun n => STGap (opt₁ := opt₁k n) (opt₂ := opt₂k n)))

end Emergence

end

end Epiplexity
end HeytingLean

