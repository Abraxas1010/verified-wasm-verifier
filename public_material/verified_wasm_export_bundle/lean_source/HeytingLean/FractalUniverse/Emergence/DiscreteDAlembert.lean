import HeytingLean.FractalUniverse.Core.DynamicGraph
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Discrete d'Alembertian Operator

Formalizes the discrete wave operator □_G on a weighted causal graph
from Veselov's "Fractal Universe" paper (Section 5.2, Equation 6).
□_G f(v) = (1/w_v) Σ_{u≺v} (f(v)-f(u))·w_uv - (1/w_v) Σ_{v≺u} (f(u)-f(v))·w_vu
-/

namespace HeytingLean.FractalUniverse.Emergence

open Finset BigOperators

/-- Weighted causal graph extending DynamicGraph with non-negative edge weights.
    Source: Veselov Eq. (6). -/
structure WeightedCausalGraph extends Core.DynamicGraph where
  weight : (t : ℕ) → V t → V t → ℝ
  weight_nonneg : ∀ t u v, 0 ≤ weight t u v

variable {G : WeightedCausalGraph}

/-- Total weight at vertex v. -/
noncomputable def totalWeight (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    (v : G.V t) : ℝ :=
  ∑ u : G.V t, G.weight t v u

/-- Past contribution to □_G: sum over causal predecessors.
    Σ_{u: u≺v} (f(v) - f(u)) · w(u,v) -/
noncomputable def pastContribution (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (f : G.V t → ℝ) (v : G.V t) : ℝ :=
  ∑ u : G.V t, if G.E t u v then (f v - f u) * G.weight t u v else 0

/-- Future contribution to □_G: sum over causal successors.
    Σ_{u: v≺u} (f(u) - f(v)) · w(v,u) -/
noncomputable def futureContribution (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (f : G.V t → ℝ) (v : G.V t) : ℝ :=
  ∑ u : G.V t, if G.E t v u then (f u - f v) * G.weight t v u else 0

/-- The discrete d'Alembertian □_G.
    □_G f(v) = (1/w_v)(past contribution) - (1/w_v)(future contribution)
    Source: Veselov Eq. (6). -/
noncomputable def discreteDAlembert (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (f : G.V t → ℝ) (v : G.V t) : ℝ :=
  let w_v := totalWeight G t v
  (1 / w_v) * pastContribution G t f v - (1 / w_v) * futureContribution G t f v

/-- Constants are in the kernel of □_G: □_G(c) = 0. -/
theorem dAlembert_const (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (c : ℝ) (v : G.V t) :
    discreteDAlembert G t (fun _ => c) v = 0 := by
  unfold discreteDAlembert pastContribution futureContribution
  simp [sub_self, zero_mul]

/-- The zero function maps to zero under □_G. -/
theorem dAlembert_zero (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (v : G.V t) :
    discreteDAlembert G t (fun _ => (0 : ℝ)) v = 0 :=
  dAlembert_const G t 0 v

/-- □_G is shift-invariant: adding a constant to f does not change □_G f.
    This strengthens the kernel property: not only do constants map to zero,
    but the operator depends only on the differences f(v) - f(u). -/
theorem dAlembert_shift_invariant (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (f : G.V t → ℝ) (c : ℝ) (v : G.V t) :
    discreteDAlembert G t (fun x => f x + c) v = discreteDAlembert G t f v := by
  unfold discreteDAlembert
  have hp : pastContribution G t (fun x => f x + c) v = pastContribution G t f v := by
    unfold pastContribution; apply Finset.sum_congr rfl; intros; split_ifs <;> ring
  have hf : futureContribution G t (fun x => f x + c) v = futureContribution G t f v := by
    unfold futureContribution; apply Finset.sum_congr rfl; intros; split_ifs <;> ring
  rw [hp, hf]

end HeytingLean.FractalUniverse.Emergence
