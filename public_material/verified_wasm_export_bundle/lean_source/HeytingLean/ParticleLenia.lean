/-
  Verified Particle Lenia

  A formally verified implementation of Particle Lenia artificial life simulation.
  This module provides:

  1. Fixed-point arithmetic for verified compilation
  2. Kernel and energy functions (Gaussian approximation, repulsion)
  3. Euler integration dynamics
  4. Stability analysis and closure operator

  The key insight is that stable Particle Lenia configurations are
  fixed points of a closure operator, connecting to the Heyting nucleus
  framework in HeytingLean.

  Reference: https://google-research.github.io/self-organising-systems/particle-lenia/
-/

import HeytingLean.ParticleLenia.Basic
import HeytingLean.ParticleLenia.Kernel
import HeytingLean.ParticleLenia.Energy
import HeytingLean.ParticleLenia.Dynamics

namespace HeytingLean
namespace ParticleLenia

/-! ## Module Summary

### Types
- `FixedPoint`: Fixed-point number (Int with implicit scale 1000)
- `Vec2`: 2D vector in fixed-point
- `Particle`: A single particle with position
- `ParticleSystem n`: A configuration of n particles
- `LeniaParams`: Simulation parameters (μ_K, σ_K, μ_G, σ_G, c_rep, dt)

### Core Functions
- `kernel`: Gaussian kernel K(r) approximation
- `growth`: Growth field G(U)
- `repulsion`: Repulsion potential R(d)
- `energyAt`: Energy at particle i
- `energyGradient`: Gradient of energy at particle i
- `eulerStep`: One Euler integration step
- `simulateToStability`: Iterate until stable

### Key Theorems
- `kernel_nonneg`: K(r) ≥ 0
- `kernel_bounded`: K(r) ≤ 1
- `growth_nonneg`: G(U) ≥ 0
- `growth_bounded`: G(U) ≤ 1
- `stable_is_fixed`: Stable configs are fixed points
- `closure_idempotent`: close(close(x)) = close(x)
- `energy_nonincreasing`: E decreases under Euler steps

### Usage

```lean
-- Create default parameters
let params := LeniaParams.default

-- Create a particle system
let particles : Fin 10 → Particle := fun i =>
  ⟨⟨⟨i.val * 100⟩, ⟨0⟩⟩⟩

-- Perform simulation steps
let particles' := eulerSteps particles params 100

-- Check stability
let stable := isStableDecide particles' params ⟨10⟩
```
-/

-- Key definitions are available via the imports above:
-- From Basic: FixedPoint, Vec2, Particle, LeniaParams, ParticleSystem, SCALE
-- From Kernel: kernel, growth, repulsion
-- From Energy: energyAt, energyGradient, totalEnergy
-- From Dynamics: eulerStep, eulerSteps, isStable, simulateToStability

end ParticleLenia
end HeytingLean
