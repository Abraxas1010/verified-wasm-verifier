import HeytingLean.Ontology.DriverChain
import HeytingLean.PerspectivalPlenum.ProjectionObligations

/-!
# Ontology.SheafGlueMatrix

Formal matrix packaging of core sheaf-glue / projection obligations used by
the R-nucleus -> J-ratchet -> driver chain.

This file does not add new axioms; it composes already-proved hooks into a
single theorem surface for ATP/export tooling.
-/

namespace HeytingLean
namespace Ontology

open PerspectivalPlenum
open PerspectivalPlenum.LensSheaf
open Representations.Radial

/-- Edge: Re-entry nucleus induces an Euler/sheaf glue witness. -/
theorem matrix_edge_rnucleus_sheaf
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    ∃ m : MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj),
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) m ∧
        (m.sec PUnit.unit).1 = (supported_oscillation (R := R)).enhances :=
  reentry_nucleus_euler_sheaf_glue (R := R)

/-- Edge: Driver package yields the same sheaf glue witness. -/
theorem matrix_edge_driver_sheaf
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α)
    {G : RadialGraph} (js : JRatchet.JState G) :
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
      (eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
        (reentry_supported_enhances_eulerPhaseLaw (R := R)) ) :=
  reentry_driverWitness_sheafGlue (R := R) (js := js)

/-- Edge: J-ratchet trajectory contract (driver projection). -/
theorem matrix_edge_jratchet_driver
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α)
    {G : RadialGraph} (js : JRatchet.JState G) :
    Topos.JRatchet.RatchetTrajectory (JRatchet.JState.spentFuel js) :=
  reentry_driverWitness_ratchetTrajectory (R := R) (js := js)

/--
Core plenum projection obligations packaged as one conjunction for direct
discharge in ATP lanes.
-/
theorem matrix_projection_core :
    ProjectionObligations.keyName .triangleCechH1 = "triangle_cech_h1" ∧
      ProjectionObligations.keyName .triangleLocalGlobal = "triangle_local_global" ∧
      ProjectionObligations.keyName .squareCircleLensRelative = "square_circle_lens_relative" ∧
      ProjectionObligations.keyName .euclideanSingletonGlues = "euclidean_singleton_glues" ∧
      ProjectionObligations.keyName .crossLensRoundtrip = "cross_lens_roundtrip" ∧
      ContextualityEngine.HasCechH1
        Quantum.Contextuality.Triangle.X
        Quantum.Contextuality.Triangle.cover
        Quantum.Contextuality.Triangle.model
        (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC) ∧
      (ContextualityEngine.LocallyAdmissibleOnCover Quantum.Contextuality.Triangle.model ∧
        ContextualityEngine.GloballyObstructed
          Quantum.Contextuality.Triangle.X
          Quantum.Contextuality.Triangle.cover
          Quantum.Contextuality.Triangle.model
          (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC)) ∧
      (Lens.CollapseToBottom Lens.Examples.euclideanLens Lens.Examples.ShapeObject.squareCircle ∧
        Lens.LocallySatisfiable Lens.Examples.higherDimLens Lens.Examples.ShapeObject.squareCircle) ∧
      Amalgamates
        LensSheaf.Examples.ShapeWitnessPresheaf
        LensSheaf.Examples.euclideanObj
        (singletonCover LensSheaf.Examples.euclideanObj)
        LensSheaf.Examples.euclideanSingletonFamily := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact ProjectionObligations.triangle_cech_h1_hook
  · exact ProjectionObligations.triangle_local_global_hook
  · exact ProjectionObligations.square_circle_lens_relative_hook
  · exact ProjectionObligations.euclidean_singleton_glues_hook

/--
Unified matrix bundle for the core ontology edges:
R nucleus -> sheaf glue, driver -> sheaf glue, J-ratchet trajectory,
plus the plenum projection core.
-/
theorem sheaf_glue_matrix_core
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α)
    {G : RadialGraph} (js : JRatchet.JState G) :
    (∃ m : MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj),
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) m ∧
        (m.sec PUnit.unit).1 = (supported_oscillation (R := R)).enhances) ∧
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
        (eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
          (reentry_supported_enhances_eulerPhaseLaw (R := R)) ) ∧
      Topos.JRatchet.RatchetTrajectory (JRatchet.JState.spentFuel js) ∧
      (ProjectionObligations.keyName .triangleCechH1 = "triangle_cech_h1" ∧
        ProjectionObligations.keyName .triangleLocalGlobal = "triangle_local_global" ∧
        ProjectionObligations.keyName .squareCircleLensRelative = "square_circle_lens_relative" ∧
        ProjectionObligations.keyName .euclideanSingletonGlues = "euclidean_singleton_glues" ∧
        ProjectionObligations.keyName .crossLensRoundtrip = "cross_lens_roundtrip" ∧
        ContextualityEngine.HasCechH1
          Quantum.Contextuality.Triangle.X
          Quantum.Contextuality.Triangle.cover
          Quantum.Contextuality.Triangle.model
          (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC) ∧
        (ContextualityEngine.LocallyAdmissibleOnCover Quantum.Contextuality.Triangle.model ∧
          ContextualityEngine.GloballyObstructed
            Quantum.Contextuality.Triangle.X
            Quantum.Contextuality.Triangle.cover
            Quantum.Contextuality.Triangle.model
            (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC)) ∧
        (Lens.CollapseToBottom Lens.Examples.euclideanLens Lens.Examples.ShapeObject.squareCircle ∧
          Lens.LocallySatisfiable Lens.Examples.higherDimLens Lens.Examples.ShapeObject.squareCircle) ∧
        Amalgamates
          LensSheaf.Examples.ShapeWitnessPresheaf
          LensSheaf.Examples.euclideanObj
          (singletonCover LensSheaf.Examples.euclideanObj)
          LensSheaf.Examples.euclideanSingletonFamily) := by
  exact ⟨
    matrix_edge_rnucleus_sheaf (R := R),
    matrix_edge_driver_sheaf (R := R) (js := js),
    matrix_edge_jratchet_driver (R := R) (js := js),
    matrix_projection_core
  ⟩

end Ontology
end HeytingLean

