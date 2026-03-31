import HeytingLean.FractalUniverse.Extraction.GraphSimulator
import HeytingLean.FractalUniverse.Core.DynamicGraph

/-!
# Bounded Growth Trajectory: CDT Exemplar

REUSABLE ABSTRACTION: extracts the bounded-growth pattern from
FractalUniverse's GraphSimulator into a standalone structure.

The `accumVertices` trajectory from `GraphSimulator.lean` is a concrete
instance of bounded coinductive growth:
- Strictly monotone (at least 1 new vertex per step)
- Lower bound: initial + t ≤ trajectory t
- Upper bound: trajectory t ≤ initial + t · max_step

This module packages these properties into `BoundedGrowthTrajectory`
and constructs an instance from any `SimulationOracle`, proving backward
compatibility with FractalUniverse's existing theorems.

Downstream consumer: `Ontology.CoinductiveBounded.Core` (the trajectory
pattern matches its observation/bounded interface).
-/

namespace HeytingLean.FractalUniverse.Bridges

open Extraction

/-- A bounded growth trajectory: a monotone ℕ-indexed sequence
    with tight linear upper and lower bounds.
    This is the interface that CoinductiveBounded consumers instantiate. -/
structure BoundedGrowthTrajectory where
  /-- The trajectory function. -/
  trajectory : ℕ → ℕ
  /-- Initial value. -/
  initial : ℕ
  /-- Maximum per-step growth. -/
  max_step : ℕ
  max_step_pos : 0 < max_step
  /-- The trajectory starts at initial. -/
  at_zero : trajectory 0 = initial
  /-- Strict monotonicity. -/
  strict_mono : ∀ t, trajectory t < trajectory (t + 1)
  /-- Lower bound: initial + t ≤ trajectory t. -/
  lower : ∀ t, initial + t ≤ trajectory t
  /-- Upper bound: trajectory t ≤ initial + t * max_step. -/
  upper : ∀ t, trajectory t ≤ initial + t * max_step

/-- Construct a BoundedGrowthTrajectory from a SimulationOracle.
    This shows FractalUniverse's CDT simulation is a concrete instance
    of bounded coinductive growth. All fields are proved by direct
    reuse of existing GraphSimulator theorems. -/
def ofSimulationOracle {cfg : SimulationConfig}
    (oracle : SimulationOracle cfg) (n₀ : ℕ) :
    BoundedGrowthTrajectory where
  trajectory := accumVertices oracle n₀
  initial := n₀
  max_step := cfg.max_new_per_step
  max_step_pos := cfg.max_new_pos
  at_zero := accumVertices_zero oracle n₀
  strict_mono := fun t => accumVertices_lt_succ oracle n₀ t
  lower := fun t => accumVertices_lower_bound oracle n₀ t
  upper := fun t => accumVertices_upper_bound oracle n₀ t

/-- Any bounded growth trajectory is strictly monotone (immediate). -/
theorem BoundedGrowthTrajectory.strictMono_trajectory (bgt : BoundedGrowthTrajectory) :
    StrictMono bgt.trajectory := by
  intro a b hab
  induction hab with
  | refl => exact bgt.strict_mono a
  | step hab ih => exact lt_trans ih (bgt.strict_mono _)

end HeytingLean.FractalUniverse.Bridges
