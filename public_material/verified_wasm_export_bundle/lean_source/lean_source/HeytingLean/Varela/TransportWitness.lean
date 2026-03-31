import HeytingLean.ClosingTheLoop.Semantics.NucleusFixedPoints
import HeytingLean.Varela.ReentryNucleus

/-!
# Varela Transport Witness

This file packages the completed Varela nucleus formalization as a **finite witness**
for the repo's broader re-entry transport vocabulary.

Theorems here are intentionally Varela-local:
- fixedness under `stageClosure`,
- membership in the closed part `stageNucleus.toSublocale`,
- recovery of the concrete ECI carrier,
- transport of order information through the witness.

This module does **not** attempt to instantiate the full OTM/Genesis bridge stack.
Its purpose is to provide an executable honesty oracle that future abstract bridge work
can be checked against.
-/

namespace HeytingLean.Varela

open ReentryStage

/-- Varela-local transport: stage-closure fixedness implies closed-part membership. -/
theorem transport_reentry_fixed_to_stageClosed {s : ReentryStage} :
    stageClosure s = s →
      s ∈ (stageNucleus.toSublocale : Set ReentryStage) := by
  intro hs
  rw [mem_stageOmega_iff_stageClosure_fixed]
  exact hs

/-- Reverse Varela-local transport: closed-part membership implies fixedness. -/
theorem transport_stageClosed_to_reentry_fixed {s : ReentryStage} :
    s ∈ (stageNucleus.toSublocale : Set ReentryStage) →
      stageClosure s = s := by
  intro hs
  rw [mem_stageOmega_iff_stageClosure_fixed] at hs
  exact hs

/-- Packed fixedness/closedness equivalence on the ambient Varela stage carrier. -/
theorem transport_reentry_fixed_iff_stageClosed {s : ReentryStage} :
    stageClosure s = s ↔
      s ∈ (stageNucleus.toSublocale : Set ReentryStage) := by
  constructor
  · exact transport_reentry_fixed_to_stageClosed
  · exact transport_stageClosed_to_reentry_fixed

/-- Closed-part membership recovers exactly the image of the concrete ECI carrier. -/
theorem transport_stageClosed_iff_eci_image {s : ReentryStage} :
    s ∈ (stageNucleus.toSublocale : Set ReentryStage) ↔
      ∃ x : IndVal, eciToStage x = s := by
  exact mem_stageOmega_iff_eci_image

/-- The latent stage is the unique ambient point excluded from the closed witness. -/
theorem latent_not_stageClosed :
    ReentryStage.latent ∉ (stageNucleus.toSublocale : Set ReentryStage) := by
  intro hs
  exact mem_stageOmega_ne_latent hs rfl

/-- Transport from an ambient closed witness down to the concrete ECI carrier. -/
theorem transport_stageOmega_to_eci (s : StageOmega) :
    eciToOmega (stageToECI s) = s := by
  exact eciToOmega_stageToECI s

/-- Transport from a concrete ECI value into the ambient closed witness. -/
theorem transport_eci_to_stageOmega (x : IndVal) :
    stageToECI (eciToOmega x) = x := by
  exact stageToECI_eciToOmega x

/-- The witness transports order information faithfully, not just carrier membership. -/
theorem transport_stageClosed_order_reflects {a b : StageOmega} :
    stageToECI a ≤ stageToECI b ↔ a ≤ b := by
  exact stageToECI_le_iff

end HeytingLean.Varela
