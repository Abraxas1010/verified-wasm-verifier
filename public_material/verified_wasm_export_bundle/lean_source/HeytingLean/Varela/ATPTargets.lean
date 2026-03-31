import HeytingLean.Varela.OTMCompanion

/-!
# Varela ATP Targets

Named prove/refute targets for the finite Varela witness.
-/

namespace HeytingLean.Varela

theorem target_varela_autonomous_fixed :
    stageClosure ReentryStage.autonomous = ReentryStage.autonomous := by
  rfl

theorem target_varela_marked_closed :
    StageClosed ReentryStage.marked := by
  exact genesis_companion_transport_reentry_fixed_to_closed rfl

theorem target_varela_marked_eci_image :
    ∃ x : IndVal, eciToStage x = ReentryStage.marked := by
  exact (genesis_companion_transport_stabilizes_iff_eci_image (s := ReentryStage.marked)).mp rfl

theorem target_varela_otm_latent_reclassifies_to_autonomous :
    ((otmCompanionReclassify ReentryStage.latent : StageOmega) : ReentryStage) =
      ReentryStage.autonomous := by
  exact otm_companion_latent_reclassifies_to_autonomous

theorem target_varela_genesis_autonomous_closed :
    GenesisCompanionClosed ReentryStage.autonomous := by
  exact genesis_companion_transport_reentry_fixed_to_closed rfl

theorem target_varela_latent_not_fixed :
    stageClosure ReentryStage.latent ≠ ReentryStage.latent := by
  exact latent_not_fixed

theorem target_varela_not_all_stages_closed :
    ¬ ∀ s : ReentryStage, StageClosed s := by
  exact not_all_stages_are_closed

theorem target_varela_latent_not_reclassify_fixed :
    ((otmCompanionReclassify ReentryStage.latent : StageOmega) : ReentryStage) ≠
      ReentryStage.latent := by
  exact otm_companion_latent_not_reclassify_fixed

theorem target_varela_autonomous_not_classical :
    ¬ (eciToOmega .autonomous ⊔ (eciToOmega .autonomous)ᶜ = (⊤ : StageOmega)) := by
  exact autonomous_point_remains_nonclassical

end HeytingLean.Varela
