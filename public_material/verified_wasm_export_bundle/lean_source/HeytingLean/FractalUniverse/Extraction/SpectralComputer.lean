import HeytingLean.FractalUniverse.Core.SpectralDimension

/-!
# Spectral Dimension Computation

Formalizes the σ-step transition probability matrix P^σ and the
diagonal return probability for spectral dimension computation,
as required by Veselov's numerical experiments (Section 7.2).

## Transition probability matrix

`transitionProb W u v σ` is P^σ(u,v): the probability of transitioning
from vertex u to vertex v in exactly σ random walk steps. This is the
σ-fold iterated matrix multiplication of the transition matrix.

## Key results

- `transitionProb_stochastic`: P^σ is row-stochastic (∑_v P^σ(u,v) = 1)
- `transitionProb_le_one`: every entry is at most 1 (by stochasticity)
- `returnProbDiag`: the diagonal P^σ(v,v) is the correct return
  probability for spectral dimension computation, lying in [0,1]

Source: Veselov Section 7.2, spectral dimension measurement via random walks.
-/

namespace HeytingLean.FractalUniverse.Extraction

open scoped BigOperators

/-- σ-step transition probability: P^σ(u,v) is the probability of
    reaching vertex v from vertex u in exactly σ random walk steps.
    Defined by iterated matrix multiplication of the one-step transition.
    P⁰ = I (identity), P^{σ+1}(u,v) = ∑_w P(u,w) · P^σ(w,v). -/
noncomputable def transitionProb {G : Core.DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : Core.RandomWalk G t) (u v : G.V t) : ℕ → ℝ
  | 0 => if u = v then 1 else 0
  | σ + 1 => ∑ w : G.V t, W.transition u w * transitionProb W w v σ

/-- P⁰ is the identity matrix: P⁰(v,v) = 1. -/
theorem transitionProb_zero_self {G : Core.DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : Core.RandomWalk G t) (v : G.V t) :
    transitionProb W v v 0 = 1 := by
  simp [transitionProb]

/-- P⁰ is the identity matrix: P⁰(u,v) = 0 for u ≠ v. -/
theorem transitionProb_zero_neq {G : Core.DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : Core.RandomWalk G t) (u v : G.V t) (h : u ≠ v) :
    transitionProb W u v 0 = 0 := by
  simp [transitionProb, h]

/-- Every entry of P^σ is non-negative (by induction on σ).
    Base: identity matrix entries ∈ {0, 1}. Step: sum of products
    of non-negative values (transition probs × inductive hypothesis). -/
theorem transitionProb_nonneg {G : Core.DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : Core.RandomWalk G t) (u v : G.V t) (σ : ℕ) :
    0 ≤ transitionProb W u v σ := by
  induction σ generalizing u v with
  | zero =>
    unfold transitionProb
    split <;> norm_num
  | succ σ ih =>
    show 0 ≤ ∑ w : G.V t, W.transition u w * transitionProb W w v σ
    exact Finset.sum_nonneg fun w _ => mul_nonneg (W.transition_nonneg u w) (ih w v)

/-- P^σ is row-stochastic: ∑_v P^σ(u,v) = 1 for all u.
    Base: ∑_v δ(u,v) = 1. Step: swap sums, factor out the constant
    transition weight, apply the inductive hypothesis, then use the
    one-step stochastic property. -/
theorem transitionProb_stochastic {G : Core.DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : Core.RandomWalk G t) (u : G.V t) (σ : ℕ) :
    ∑ v : G.V t, transitionProb W u v σ = 1 := by
  induction σ generalizing u with
  | zero =>
    simp [transitionProb, Finset.sum_ite_eq]
  | succ σ ih =>
    simp only [transitionProb]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ih, mul_one]
    exact W.transition_stochastic u

/-- Every entry of P^σ is at most 1. Each entry is one non-negative
    term of a sum that equals 1 (row-stochastic), hence ≤ 1. -/
theorem transitionProb_le_one {G : Core.DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : Core.RandomWalk G t) (u v : G.V t) (σ : ℕ) :
    transitionProb W u v σ ≤ 1 := by
  calc transitionProb W u v σ
      ≤ ∑ v' : G.V t, transitionProb W u v' σ :=
        Finset.single_le_sum (fun i _ => transitionProb_nonneg W u i σ)
          (Finset.mem_univ v)
    _ = 1 := transitionProb_stochastic W u σ

/-- The diagonal return probability: P^σ(v,v), i.e., the probability
    of returning to vertex v after exactly σ random walk steps.
    This is the correct quantity for spectral dimension computation:
    D_s = -2 · lim_{σ→∞} log P^σ(v,v) / log σ. -/
noncomputable def returnProbDiag {G : Core.DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : Core.RandomWalk G t) (v : G.V t) (σ : ℕ) : ℝ :=
  transitionProb W v v σ

/-- The return probability at σ = 0 is 1 (the walk starts at v). -/
theorem returnProbDiag_zero {G : Core.DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : Core.RandomWalk G t) (v : G.V t) :
    returnProbDiag W v 0 = 1 :=
  transitionProb_zero_self W v

/-- The return probability lies in [0, 1] for all σ.
    Non-negativity: induction + multiplication of non-negatives.
    Upper bound: single term of a unit row sum. -/
theorem returnProbDiag_unit_interval {G : Core.DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : Core.RandomWalk G t) (v : G.V t) (σ : ℕ) :
    0 ≤ returnProbDiag W v σ ∧ returnProbDiag W v σ ≤ 1 :=
  ⟨transitionProb_nonneg W v v σ, transitionProb_le_one W v v σ⟩

end HeytingLean.FractalUniverse.Extraction
