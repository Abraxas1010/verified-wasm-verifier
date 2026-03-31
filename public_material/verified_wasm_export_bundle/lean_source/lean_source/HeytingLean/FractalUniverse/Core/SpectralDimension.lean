import HeytingLean.FractalUniverse.Core.DynamicGraph
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Spectral Dimension Preliminaries

Defines the random walk return probability and scale-dependent spectral
dimension ratio from Veselov's "Fractal Universe" paper (Section 2.2).
The spectral dimension D_s = -2 · lim_{σ→∞} log P(σ) / log σ is defined
as a `Filter.Tendsto` limit via `HasSpectralDimValue`.
-/

namespace HeytingLean.FractalUniverse.Core

open scoped BigOperators

/-- Random walk on a graph at time t.
    Source: Veselov Section 2.2. -/
structure RandomWalk (G : DynamicGraph) (t : ℕ) [Fintype (G.V t)] where
  /-- Transition probability from u to v. -/
  transition : G.V t → G.V t → ℝ
  /-- Non-negativity. -/
  transition_nonneg : ∀ u v, 0 ≤ transition u v
  /-- Row-stochastic. -/
  transition_stochastic : ∀ u, ∑ v : G.V t, transition u v = 1

/-- Return probability after σ steps (σ-th power of transition matrix, diagonal entry).
    For Fintype vertex sets, this is well-defined via iterated matrix composition. -/
noncomputable def returnProb {G : DynamicGraph} {t : ℕ} [Fintype (G.V t)]
    (W : RandomWalk G t) (v : G.V t) : ℕ → ℝ
  | 0 => 1
  | σ + 1 => ∑ u, W.transition v u * returnProb W u σ

/-- Return probability is non-negative (by induction). -/
theorem returnProb_nonneg {G : DynamicGraph} {t : ℕ} [Fintype (G.V t)]
    (W : RandomWalk G t) (v : G.V t) (σ : ℕ) : 0 ≤ returnProb W v σ := by
  induction σ generalizing v with
  | zero => simp [returnProb]
  | succ σ ih =>
    unfold returnProb
    apply Finset.sum_nonneg
    intro u _
    exact mul_nonneg (W.transition_nonneg v u) (ih u)

/-- Return probability at step 0 is 1 (the walk starts at v). -/
theorem returnProb_zero {G : DynamicGraph} {t : ℕ} [Fintype (G.V t)]
    (W : RandomWalk G t) (v : G.V t) : returnProb W v 0 = 1 := rfl

/-- Scale-dependent spectral dimension (as a function, without taking the limit).
    The actual spectral dimension is the limit of this ratio as σ → ∞. -/
noncomputable def spectralDimRatio {G : DynamicGraph} {t : ℕ} [Fintype (G.V t)]
    (W : RandomWalk G t) (v : G.V t) (σ : ℕ) : ℝ :=
  if σ = 0 then 0
  else -2 * Real.log (returnProb W v σ) / Real.log σ

/-- A graph has spectral dimension D_s at vertex v if the scale-dependent
    ratio converges to D_s as σ → ∞. This is the formal statement of
    D_s = -2 · lim_{σ→∞} log P(σ) / log σ from Veselov Eq. (2). -/
def HasSpectralDimValue {G : DynamicGraph} {t : ℕ} [Fintype (G.V t)]
    (W : RandomWalk G t) (v : G.V t) (D_s : ℝ) : Prop :=
  Filter.Tendsto (fun σ : ℕ => spectralDimRatio W v σ) Filter.atTop (nhds D_s)

end HeytingLean.FractalUniverse.Core
