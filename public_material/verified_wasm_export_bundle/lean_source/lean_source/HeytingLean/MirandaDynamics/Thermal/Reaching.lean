import HeytingLean.MirandaDynamics.TKFT.Reaching
import HeytingLean.MirandaDynamics.External.Interfaces
import HeytingLean.MirandaDynamics.Thermal.Basic
import HeytingLean.MirandaDynamics.Thermal.SafetyPredicates

/-!
# MirandaDynamics.Thermal: reaching semantics (interface-first)

This file defines a TKFT-style reaching relation for thermal state transitions.

We deliberately keep the physics content behind explicit *data interfaces* so that downstream
logical theorems are honest and auditable.

The reaching relation models: given a thermal state, which future states are reachable
under the thermal dynamics of the system?
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal

open HeytingLean.MirandaDynamics.TKFT

/-- A minimal thermal dynamics model.

This abstracts the physics of heat transfer and thermal response.
A concrete implementation would be instantiated from measured thermal parameters.
-/
structure ThermalDynamicsModel where
  /-- Predict temperature at time t+dt given current temperature and power. -/
  predict_temp : (currentC : Float) → (powerW : Float) → (dt_ms : Int) → Float
  /-- Maximum expected temperature change per millisecond. -/
  max_rate_per_ms : Float

/-- A thermal transition model, abstracted over the thermal response mechanism.

`canReach s1 s2` is intended to mean "state s2 is physically reachable from s1".
-/
structure ThermalTransitionModel where
  /-- Predicate: can thermal state s2 be reached from s1? -/
  canReach : ThermalState → ThermalState → Bool

/-- Thermal reaching: a future state is reachable from a current state.

This "reaching" is physical: it is a predicate about thermodynamically feasible transitions.
-/
def reaches (M : ThermalTransitionModel) (s1 s2 : ThermalState) : Bool :=
  M.canReach s1 s2

/-- Package thermal transitions as a TKFT reaching relation.

Inputs are `(currentState, futureState)` pairs and outputs are the boolean "reachable" observation.
-/
def reachingRelOfTransition (M : ThermalTransitionModel) :
    ReachingRel (ThermalState × ThermalState) Bool :=
  ⟨fun inp out => out = reaches M inp.1 inp.2⟩

theorem reachingRelOfTransition_functional (M : ThermalTransitionModel) :
    (reachingRelOfTransition M).Functional := by
  intro inp b₁ b₂ h1 h2
  exact h1.trans h2.symm

/-- TKFT-style construction for thermal state transitions. -/
def ThermalTKFTConstruction (M : ThermalTransitionModel) :
    External.TKFTConstruction (ThermalState × ThermalState) Bool :=
  { reach := reachingRelOfTransition M
    functional := reachingRelOfTransition_functional M }

/-! ## Safety-Preserving Transitions -/

/-- A transition model that preserves safety invariants.

This wraps a base model with the constraint that safe states
only transition to safe states.
-/
structure SafeTransitionModel extends ThermalTransitionModel where
  /-- If source is safe and transition is possible, target must be safe. -/
  preserves_safety : ∀ s1 s2,
    isSafeStateDecide s1 = true →
    canReach s1 s2 = true →
    isSafeStateDecide s2 = true

/-- A conservative transition model that only allows temperature decreases
    when above warning threshold. -/
def conservativeModel : ThermalTransitionModel where
  canReach := fun s1 s2 =>
    -- Time must advance
    s2.timestamp_ms > s1.timestamp_ms &&
    -- Temperature changes must be bounded
    (s1.zones.zip s2.zones).all fun (z1, z2) =>
      -- Zone IDs must match
      z1.1 == z2.1 &&
      -- Temperature change is bounded by max rate
      (z2.2 - z1.2).abs < 10.0  -- Conservative: max 10°C change between samples

/-! ## Reaching Relation for Safety Verification -/

/-- Reaching relation specialized for safety verification.

This relation connects thermal states to their safety status.
-/
def safetyReachingRel : ReachingRel ThermalState Bool :=
  ⟨fun s b => b = isSafeStateDecide s⟩

theorem safetyReachingRel_functional : safetyReachingRel.Functional := by
  intro s b₁ b₂ h1 h2
  exact h1.trans h2.symm

/-- TKFT construction for safety verification. -/
def SafetyTKFTConstruction : External.TKFTConstruction ThermalState Bool :=
  { reach := safetyReachingRel
    functional := safetyReachingRel_functional }

/-! ## Multi-step Reaching -/

/-- A thermal trajectory is a sequence of states over time. -/
structure ThermalTrajectory where
  states : Array ThermalState
  /-- States are ordered by timestamp. -/
  ordered : ∀ i j : Fin states.size, i.val < j.val →
    states[i].timestamp_ms < states[j].timestamp_ms

/-- A trajectory is safe if all states in it are safe. -/
def safeTrajectory (traj : ThermalTrajectory) : Prop :=
  ∀ i : Fin traj.states.size, isSafeStateDecide traj.states[i] = true

/-- Multi-step reaching: can we reach state sn from s0 through a trajectory? -/
def multiStepReaches (M : ThermalTransitionModel) (traj : ThermalTrajectory) : Bool :=
  if traj.states.size < 2 then true
  else
    -- Check each consecutive pair using safe indexing
    (List.range (traj.states.size - 1)).all fun i =>
      match traj.states[i]?, traj.states[i + 1]? with
      | some s1, some s2 => M.canReach s1 s2
      | _, _ => true

end Thermal
end MirandaDynamics
end HeytingLean
