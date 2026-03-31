import HeytingLean.FractalUniverse.Core.DynamicGraph

/-!
# CDT Graph Simulation Specification

Formalizes the specification of a Causal Dynamical Triangulation (CDT)
graph simulator from Veselov's computational experiments (Section 7).

A `SimulationOracle` specifies how many vertices to add at each step,
subject to a `SimulationConfig` that bounds the growth rate. The
accumulated vertex trajectory `accumVertices` is shown to be strictly
monotone with tight linear bounds: n₀ + t ≤ accumVertices ≤ n₀ + t · M.

This module provides the mathematical foundation for verified CDT
simulation: any implementation satisfying the oracle contract produces
a trajectory with the proved growth properties.
-/

namespace HeytingLean.FractalUniverse.Extraction

/-- Configuration for a CDT graph growth simulation.
    Bounds the maximum number of new vertices per step.
    Source: Veselov Section 7 computational experiments. -/
structure SimulationConfig where
  /-- Upper bound on new vertices added per simulation step. -/
  max_new_per_step : ℕ
  /-- At least one new vertex per step (non-degenerate growth). -/
  max_new_pos : 0 < max_new_per_step

/-- A simulation oracle specifying the exact number of new vertices
    at each time step, consistent with a `SimulationConfig`. -/
structure SimulationOracle (cfg : SimulationConfig) where
  /-- Number of new vertices at time step t. -/
  new_count : ℕ → ℕ
  /-- Growth is non-degenerate: at least one new vertex per step. -/
  new_count_pos : ∀ t, 0 < new_count t
  /-- Growth respects the config bound. -/
  new_count_bounded : ∀ t, new_count t ≤ cfg.max_new_per_step

/-- Accumulated vertex count after t simulation steps starting from n₀
    initial vertices. Models the total size of the CDT graph at step t. -/
def accumVertices {cfg : SimulationConfig} (oracle : SimulationOracle cfg)
    (n₀ : ℕ) : ℕ → ℕ
  | 0 => n₀
  | t + 1 => accumVertices oracle n₀ t + oracle.new_count t

@[simp]
theorem accumVertices_zero {cfg : SimulationConfig}
    (oracle : SimulationOracle cfg) (n₀ : ℕ) :
    accumVertices oracle n₀ 0 = n₀ := rfl

@[simp]
theorem accumVertices_succ {cfg : SimulationConfig}
    (oracle : SimulationOracle cfg) (n₀ t : ℕ) :
    accumVertices oracle n₀ (t + 1) =
      accumVertices oracle n₀ t + oracle.new_count t := rfl

/-- Vertex count strictly increases at each step. The oracle adds at
    least one new vertex per step, so the trajectory is strictly monotone. -/
theorem accumVertices_lt_succ {cfg : SimulationConfig}
    (oracle : SimulationOracle cfg) (n₀ t : ℕ) :
    accumVertices oracle n₀ t < accumVertices oracle n₀ (t + 1) := by
  simp only [accumVertices_succ]
  have := oracle.new_count_pos t
  omega

/-- Lower bound: after t steps, at least t new vertices have been added.
    Proof by induction: each step adds ≥ 1, so total growth ≥ t. -/
theorem accumVertices_lower_bound {cfg : SimulationConfig}
    (oracle : SimulationOracle cfg) (n₀ t : ℕ) :
    n₀ + t ≤ accumVertices oracle n₀ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [accumVertices_succ]
    have := oracle.new_count_pos t
    omega

/-- Upper bound: growth is bounded by the per-step maximum.
    After t steps, at most t · max_new_per_step vertices were added.
    Proof by induction with telescoping via `Nat.add_le_add`. -/
theorem accumVertices_upper_bound {cfg : SimulationConfig}
    (oracle : SimulationOracle cfg) (n₀ t : ℕ) :
    accumVertices oracle n₀ t ≤ n₀ + t * cfg.max_new_per_step := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [accumVertices_succ]
    calc accumVertices oracle n₀ t + oracle.new_count t
        ≤ (n₀ + t * cfg.max_new_per_step) + cfg.max_new_per_step :=
          Nat.add_le_add ih (oracle.new_count_bounded t)
      _ = n₀ + (t + 1) * cfg.max_new_per_step := by
          rw [Nat.succ_mul, Nat.add_assoc]

end HeytingLean.FractalUniverse.Extraction
