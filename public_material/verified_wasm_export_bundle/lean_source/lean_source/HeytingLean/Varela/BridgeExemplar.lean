import HeytingLean.Varela.TransportWitness

/-!
# Varela Bridge Exemplar

This file gives the smallest honest companion to the repo's abstract re-entry
transport vocabulary. It does not import or instantiate the abstract Genesis/OTM
bridge files. Instead it packages the already-shipped finite witness in a shape that
future bridge work can cite without overclaiming.
-/

namespace HeytingLean.Varela

/-- Varela-local notion of "closed" for the ambient stage carrier. -/
def StageClosed (s : ReentryStage) : Prop :=
  s ∈ (stageNucleus.toSublocale : Set ReentryStage)

/-- The worked exemplar: re-entry fixedness matches closed-part membership locally. -/
theorem exemplar_reentry_fixed_iff_stage_closed {s : ReentryStage} :
    stageClosure s = s ↔ StageClosed s := by
  exact transport_reentry_fixed_iff_stageClosed

/-- The same exemplar, phrased as fixedness compatibility. -/
theorem exemplar_transport_compat_with_stage_closure {s : ReentryStage} :
    StageClosed s ↔ stageClosure s = s := by
  exact (exemplar_reentry_fixed_iff_stage_closed (s := s)).symm

/-- Closed ambient points are exactly the image of the concrete ECI carrier. -/
theorem exemplar_stage_closed_iff_eci_image {s : ReentryStage} :
    StageClosed s ↔ ∃ x : IndVal, eciToStage x = s := by
  exact transport_stageClosed_iff_eci_image

/-- The worked exemplar packages fixedness and ECI recovery in one equivalence. -/
theorem exemplar_reentry_fixed_iff_eci_image {s : ReentryStage} :
    stageClosure s = s ↔ ∃ x : IndVal, eciToStage x = s := by
  calc
    stageClosure s = s ↔ StageClosed s := exemplar_reentry_fixed_iff_stage_closed
    _ ↔ ∃ x : IndVal, eciToStage x = s := exemplar_stage_closed_iff_eci_image

/-- The closed witness carrier is order-isomorphic to the concrete ECI carrier. -/
def exemplar_stageOmega_order_iso : StageOmega ≃o IndVal :=
  omegaOrderIsoECI

/-- Round-trip from the ambient closed witness back to itself through ECI. -/
theorem exemplar_stageOmega_roundtrip (s : StageOmega) :
    eciToOmega (stageToECI s) = s := by
  exact transport_stageOmega_to_eci s

/-- Round-trip from the concrete ECI carrier into the ambient closed witness. -/
theorem exemplar_eci_roundtrip (x : IndVal) :
    stageToECI (eciToOmega x) = x := by
  exact transport_eci_to_stageOmega x

end HeytingLean.Varela
