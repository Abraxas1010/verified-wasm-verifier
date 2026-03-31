import HeytingLean.Topos.JRatchet
import HeytingLean.Ontology.DriverChain

/-!
# JRatchetSheafGlue: collected sheaf-glue correspondence theorems

This module re-exports the key sheaf-glue theorems that bridge J-ratchet
objects to other ontological carriers (R-nucleus, ontological drivers, etc.).

The full sheaf-glue matrix is in `Ontology/SheafGlueMatrix.lean` and the
constructive tag-class normalizations are in `Ontology/ConstructiveGlueTagClasses.lean`.
Here we collect the J-ratchet-specific correspondences for the hub interface.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet

open HeytingLean.Topos.JRatchet

/-! ## Frame-level ↔ ontological driver correspondences -/

/-- Frame-level fixed-point core ↔ ontological frame-level ratchet driver. -/
theorem frameLevelCore_iff_ontologicalDriver {X : Type u} [Order.Frame X] (n : Nucleus X) :
    FrameLevelFixedPointCoreContract n ↔ OntologicalFrameLevelRatchetDriverContract n :=
  thm_sheaf_glue_j_ratchet_frame_level_j_ratchet_fixed_point_core_to_ontological_driver_frame_level_j_ratchet_fixed_point_driver n

/-- Reverse: ontological driver ↔ frame-level core. -/
theorem ontologicalDriver_iff_frameLevelCore {X : Type u} [Order.Frame X] (n : Nucleus X) :
    OntologicalFrameLevelRatchetDriverContract n ↔ FrameLevelFixedPointCoreContract n :=
  thm_sheaf_glue_ontological_driver_frame_level_j_ratchet_fixed_point_driver_to_j_ratchet_frame_level_j_ratchet_fixed_point_core n

/-! ## Radial trajectory bridge -/

/-- Radial spentFuel is a valid ratchet trajectory. -/
theorem radialSpentFuel_is_trajectory
    {G : HeytingLean.Representations.Radial.RadialGraph}
    (js : HeytingLean.Representations.Radial.JRatchet.JState G) :
    RatchetTrajectory (HeytingLean.Representations.Radial.JRatchet.JState.spentFuel js) :=
  radial_spentFuel_trajectory (js := js)

/-! ## J-trajectory equivalence (ontology anchor) -/

/-- The J-trajectory equivalence theorem from the ontology conjectures. -/
theorem jTrajectoryEquiv
    {G : HeytingLean.Representations.Radial.RadialGraph}
    (js : HeytingLean.Representations.Radial.JRatchet.JState G) :
    RatchetTrajectory (HeytingLean.Representations.Radial.JRatchet.JState.spentFuel js) :=
  ontology_jtrajectory_equiv_20260219 (js := js)

end JRatchet
end Bridges
end HeytingLean
