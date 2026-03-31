import HeytingLean.Topos.JRatchet.FrameCore
import HeytingLean.Topos.JRatchet.Guardrails
import HeytingLean.LoF.Bauer.DoubleNegation
import HeytingLean.LoF.Bauer.ToposBridge
import HeytingLean.Representations.Radial.JRatchet

/-!
# JRatchet (j): nucleus/local-operator wrapper layer

This module is the public entry point for the `WIP/j_ratchet.md` “ratchet” story:

* **Frame-level:** nuclei on frames induce fixed-point (sublocale) cores that are again Heyting.
  We expose explicit closure formulas for joins/sups (`JRatchet.FrameCore`).
* **Guardrails:** we record an explicit non-distributive lattice counterexample (`M3`) which
  blocks unsafe generalizations (“fixed points are always Heyting”).
* **Topos bridge:** a nucleus on `Prop` induces a local operator on `Type` (Bauer Phase 3).
* **Classical crust:** double-negation nucleus and the Boolean “classical core” (Bauer Phase 4).

All heavy lifting is delegated to mathlib and the already-landed Bauer modules.
-/

namespace HeytingLean
namespace Topos
namespace JRatchet

open HeytingLean.Representations.Radial

/-! Re-export a few key names under the `JRatchet` umbrella. -/

abbrev doubleNegNucleus := HeytingLean.LoF.Bauer.doubleNegNucleus
abbrev ClassicalCore := HeytingLean.LoF.Bauer.ClassicalCore
noncomputable abbrev localOperatorOfPropNucleus := HeytingLean.LoF.Bauer.localOperatorOfPropNucleus

/-- Public ratchet trajectory contract used by domain bridges (e.g. LES runs). -/
def RatchetTrajectory (level : Nat → Nat) : Prop :=
  ∀ fuel₁ fuel₂, fuel₁ ≤ fuel₂ → level fuel₁ ≤ level fuel₂

/--
Radial witness: for any radial J-state, spent-fuel growth along bounded exploration
is a valid ratchet trajectory.
-/
theorem radial_spentFuel_trajectory {G : RadialGraph}
    (js : HeytingLean.Representations.Radial.JRatchet.JState G) :
    RatchetTrajectory (HeytingLean.Representations.Radial.JRatchet.JState.spentFuel js) :=
  HeytingLean.Representations.Radial.JRatchet.JState.spentFuel_monotone (js := js)

/--
Queue anchor theorem for `ontology_jtrajectory_equiv_20260219`.

This is the concrete API witness for the `Euler Driver` statement.
-/
theorem ontology_jtrajectory_equiv_20260219
    {G : HeytingLean.Representations.Radial.RadialGraph}
    (js : HeytingLean.Representations.Radial.JRatchet.JState G) :
    RatchetTrajectory (HeytingLean.Representations.Radial.JRatchet.JState.spentFuel js) :=
  radial_spentFuel_trajectory (js := js)

/-- Contract surfaced for frame-level fixed-point core driver alignment. -/
def FrameLevelFixedPointCoreContract {X : Type u} [Order.Frame X] (n : Nucleus X) : Prop :=
  (∀ x : X, ((n.toSublocale.restrict x : n.toSublocale) : X) = n x) ∧
  (∀ a b : n.toSublocale, ((a ⊔ b : n.toSublocale) : X) = n ((a : X) ⊔ (b : X)))

/-- Ontological driver contract alias for frame-level fixed-point ratchet driver. -/
def OntologicalFrameLevelRatchetDriverContract {X : Type u} [Order.Frame X] (n : Nucleus X) : Prop :=
  FrameLevelFixedPointCoreContract n

/--
Direct correspondence for queue edge:
J-ratchet frame-level fixed-point core <-> ontological frame-level fixed-point driver.
-/
theorem thm_sheaf_glue_j_ratchet_frame_level_j_ratchet_fixed_point_core_to_ontological_driver_frame_level_j_ratchet_fixed_point_driver
    {X : Type u} [Order.Frame X] (n : Nucleus X) :
    FrameLevelFixedPointCoreContract n ↔ OntologicalFrameLevelRatchetDriverContract n := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Reverse direct correspondence for queue edge:
ontological frame-level fixed-point driver <-> J-ratchet frame-level fixed-point core.
-/
theorem thm_sheaf_glue_ontological_driver_frame_level_j_ratchet_fixed_point_driver_to_j_ratchet_frame_level_j_ratchet_fixed_point_core
    {X : Type u} [Order.Frame X] (n : Nucleus X) :
    OntologicalFrameLevelRatchetDriverContract n ↔ FrameLevelFixedPointCoreContract n := by
  exact
    (thm_sheaf_glue_j_ratchet_frame_level_j_ratchet_fixed_point_core_to_ontological_driver_frame_level_j_ratchet_fixed_point_driver
      (n := n)).symm

end JRatchet
end Topos
end HeytingLean
