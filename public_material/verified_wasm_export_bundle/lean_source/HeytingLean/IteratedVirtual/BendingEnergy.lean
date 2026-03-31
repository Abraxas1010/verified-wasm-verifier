import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.Normed.Group.Basic

/-!
# IteratedVirtual.BendingEnergy

A **nontrivial** discrete “tension/bending” energy that is not zero-by-definition.

We model a discrete curve `p : ℕ → V` in a normed additive group `V` (e.g. `ℝ³`) and define the
second-difference:

`Δ² p(k) = p(k+2) - 2•p(k+1) + p(k)`.

Then the bending energy on a prefix is:

`E(p, N) = ∑_{k < N} ‖Δ² p(k)‖²`.

Main results (strict-only):
- `E(p, N) = 0 ↔ ∀ k < N, Δ² p(k) = 0` (zero energy iff all second differences vanish).
- Vanishing second differences imply the curve is **affine** on the prefix: `p(k) = p(0) + k•d`.

This gives a mathematically honest “minimizes tension” statement: **straight** discrete curves are
exactly the zero-bending-energy curves.
-/

namespace HeytingLean
namespace IteratedVirtual

open scoped BigOperators

section Algebra

variable {V : Type} [AddCommGroup V]

/-- First difference `Δ p(k) = p(k+1) - p(k)`. -/
def firstDiff (p : Nat → V) (k : Nat) : V :=
  p (k + 1) - p k

/-- Second difference `Δ² p(k) = p(k+2) - 2•p(k+1) + p(k)`. -/
def secondDiff (p : Nat → V) (k : Nat) : V :=
  p (k + 2) - (2 : Nat) • p (k + 1) + p k

theorem firstDiff_sub_firstDiff (p : Nat → V) (k : Nat) :
    firstDiff p (k + 1) - firstDiff p k = secondDiff p k := by
  dsimp [firstDiff, secondDiff]
  -- `(a-b)-(b-c) = a - 2•b + c`
  -- `simp` is sufficient with `two_nsmul`.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, two_nsmul]

theorem firstDiff_succ_eq_of_secondDiff_eq_zero (p : Nat → V) (k : Nat)
    (h : secondDiff p k = 0) :
    firstDiff p (k + 1) = firstDiff p k := by
  have : firstDiff p (k + 1) - firstDiff p k = 0 := by
    simpa [firstDiff_sub_firstDiff (p := p) (k := k)] using h
  exact sub_eq_zero.mp this

/-- If `Δ² p(k)=0` for all `k<N`, then the first difference is constant on `k≤N`. -/
theorem firstDiff_eq_firstDiff0_of_secondDiff_eq_zero_prefix (p : Nat → V) (N : Nat)
    (h : ∀ k : Nat, k < N → secondDiff p k = 0) :
    ∀ k : Nat, k ≤ N → firstDiff p k = firstDiff p 0 := by
  intro k hk
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hk' : k ≤ N := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hk
      have hlt : k < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hstep : firstDiff p (k + 1) = firstDiff p k :=
        firstDiff_succ_eq_of_secondDiff_eq_zero (p := p) (k := k) (h := h k hlt)
      simpa [Nat.succ_eq_add_one, hstep] using ih hk'

/-- Vanishing second differences on a prefix forces an **affine** form on that prefix. -/
theorem affine_on_prefix_of_secondDiff_eq_zero (p : Nat → V) (N : Nat)
    (h : ∀ k : Nat, k < N → secondDiff p k = 0) :
    ∀ k : Nat, k ≤ N + 1 → p k = p 0 + k • (firstDiff p 0) := by
  intro k hk
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hkN : k ≤ N := by
        -- `k+1 ≤ N+1` implies `k ≤ N`
        exact Nat.le_of_succ_le_succ hk
      have hk' : k ≤ N + 1 := by
        exact Nat.le_trans (Nat.le_succ k) hk
      have hΔ : firstDiff p k = firstDiff p 0 :=
        firstDiff_eq_firstDiff0_of_secondDiff_eq_zero_prefix (p := p) (N := N) h k hkN
      have hrec : p (k + 1) = firstDiff p 0 + p k := by
        -- `p(k+1) - p(k) = Δp(0)` gives `p(k+1) = Δp(0) + p(k)`.
        have : p (k + 1) - p k = firstDiff p 0 := by
          simpa [firstDiff] using hΔ
        exact (sub_eq_iff_eq_add).1 this
      -- Plug in the IH for `p k`.
      calc
        p (k + 1) = firstDiff p 0 + p k := hrec
        _ = firstDiff p 0 + (p 0 + k • firstDiff p 0) := by simp [ih hk']
        _ = p 0 + (k + 1) • firstDiff p 0 := by
              -- Rearrange and use `succ_nsmul`.
              simp [succ_nsmul, add_left_comm, add_comm]

end Algebra

section Energy

variable {V : Type} [NormedAddCommGroup V]

/-- Discrete bending energy on the prefix `k < N`. -/
def bendingEnergy (p : Nat → V) (N : Nat) : ℝ :=
  (Finset.range N).sum (fun k => ‖secondDiff p k‖ ^ 2)

theorem bendingEnergy_nonneg (p : Nat → V) (N : Nat) : 0 ≤ bendingEnergy p N := by
  classical
  dsimp [bendingEnergy]
  refine Finset.sum_nonneg ?_
  intro k hk
  exact sq_nonneg ‖secondDiff p k‖

theorem bendingEnergy_eq_zero_iff_secondDiff_eq_zero (p : Nat → V) (N : Nat) :
    bendingEnergy p N = 0 ↔ ∀ k : Nat, k < N → secondDiff p k = 0 := by
  classical
  constructor
  · intro hE k hk
    have hterm :
        ‖secondDiff p k‖ ^ 2 = 0 := by
      -- Every term is nonnegative; if the sum is 0, each term must be 0.
      have hn : ∀ i ∈ Finset.range N, 0 ≤ ‖secondDiff p i‖ ^ 2 := by
        intro i hi
        exact sq_nonneg ‖secondDiff p i‖
      have hall : ∀ i ∈ Finset.range N, ‖secondDiff p i‖ ^ 2 = 0 := by
        -- `sum = 0` with nonneg summands.
        exact (Finset.sum_eq_zero_iff_of_nonneg hn).1 (by simpa [bendingEnergy] using hE)
      exact hall k (by simpa using hk)
    have hnorm : ‖secondDiff p k‖ = 0 := by
      -- `a^2 = 0` implies `a = 0`.
      exact (sq_eq_zero_iff (a := ‖secondDiff p k‖)).1 (by simpa using hterm)
    exact norm_eq_zero.1 hnorm
  · intro h
    -- Every term is 0, so the sum is 0.
    dsimp [bendingEnergy]
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hk' : k < N := by
      simpa using hk
    have hsd : secondDiff p k = 0 := h k hk'
    simp [hsd]

/-- Zero bending energy on a prefix implies an affine form on that prefix. -/
theorem affine_on_prefix_of_bendingEnergy_eq_zero (p : Nat → V) (N : Nat) (hE : bendingEnergy p N = 0) :
    ∀ k : Nat, k ≤ N + 1 → p k = p 0 + k • (firstDiff p 0) := by
  have hsd : ∀ k : Nat, k < N → secondDiff p k = 0 :=
    (bendingEnergy_eq_zero_iff_secondDiff_eq_zero (p := p) (N := N)).1 hE
  exact affine_on_prefix_of_secondDiff_eq_zero (p := p) (N := N) hsd

end Energy

end IteratedVirtual
end HeytingLean
