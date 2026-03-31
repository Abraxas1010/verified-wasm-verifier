import HeytingLean.Varela.Counterexamples

/-!
# Varela Genesis Companion

Finite companion to the Genesis re-entry transport lane.
-/

namespace HeytingLean.Varela

def GenesisCompanionStabilizes (s : ReentryStage) : Prop :=
  stageClosure s = s

def GenesisCompanionClosed (s : ReentryStage) : Prop :=
  StageClosed s

theorem genesis_companion_transport_reentry_fixed_to_closed {s : ReentryStage} :
    GenesisCompanionStabilizes s → GenesisCompanionClosed s := by
  exact exemplar_reentry_fixed_iff_stage_closed.mp

theorem genesis_companion_transport_closed_to_reentry_fixed {s : ReentryStage} :
    GenesisCompanionClosed s → GenesisCompanionStabilizes s := by
  exact exemplar_reentry_fixed_iff_stage_closed.mpr

theorem genesis_companion_transport_compat_with_stabilization {s : ReentryStage} :
    GenesisCompanionStabilizes s ↔ GenesisCompanionClosed s := by
  exact exemplar_reentry_fixed_iff_stage_closed

theorem genesis_companion_transport_closed_iff_eci_image {s : ReentryStage} :
    GenesisCompanionClosed s ↔ ∃ x : IndVal, eciToStage x = s := by
  exact exemplar_stage_closed_iff_eci_image

theorem genesis_companion_transport_stabilizes_iff_eci_image {s : ReentryStage} :
    GenesisCompanionStabilizes s ↔ ∃ x : IndVal, eciToStage x = s := by
  exact exemplar_reentry_fixed_iff_eci_image

theorem genesis_companion_latent_not_stabilized :
    ¬ GenesisCompanionStabilizes ReentryStage.latent := by
  exact latent_not_fixed

theorem genesis_companion_not_every_stage_stabilizes :
    ¬ ∀ s : ReentryStage, GenesisCompanionStabilizes s := by
  exact not_all_stages_are_fixed

theorem genesis_companion_not_every_stage_closed :
    ¬ ∀ s : ReentryStage, GenesisCompanionClosed s := by
  exact not_all_stages_are_closed

end HeytingLean.Varela
