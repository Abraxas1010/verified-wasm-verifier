import HeytingLean.Varela.GenesisCompanion

/-!
# Varela OTM Companion

Finite companion to the OTM re-entry fixedness / reclassification / local-closed
vocabulary.
-/

namespace HeytingLean.Varela

noncomputable def otmCompanionReclassify (s : ReentryStage) : StageOmega :=
  stageNucleus.toSublocale.restrict s

@[simp] theorem coe_otmCompanionReclassify (s : ReentryStage) :
    ((otmCompanionReclassify s : StageOmega) : ReentryStage) = stageClosure s := by
  unfold otmCompanionReclassify
  have h :
      stageNucleus.toSublocale.restrict s =
        (⟨stageNucleus s, s, rfl⟩ : StageOmega) :=
    Nucleus.restrict_toSublocale (n := stageNucleus) s
  exact congrArg Subtype.val h

def OTMCompanionLocallyClosed (s : ReentryStage) : Prop :=
  StageClosed s

theorem otm_companion_reentry_fixed_iff_reclassify_fixed {s : ReentryStage} :
    stageClosure s = s ↔ ((otmCompanionReclassify s : StageOmega) : ReentryStage) = s := by
  rw [coe_otmCompanionReclassify]

theorem otm_companion_reentry_fixed_iff_local_closed {s : ReentryStage} :
    stageClosure s = s ↔ OTMCompanionLocallyClosed s := by
  exact exemplar_reentry_fixed_iff_stage_closed

theorem otm_companion_reentry_fixed_iff_target_of_transport {s : ReentryStage}
    {P : ReentryStage → Prop}
    (htransport : OTMCompanionLocallyClosed s ↔ P s) :
    stageClosure s = s ↔ P s := by
  exact (otm_companion_reentry_fixed_iff_local_closed (s := s)).trans htransport

theorem otm_companion_reentry_fixed_iff_eci_image {s : ReentryStage} :
    stageClosure s = s ↔ ∃ x : IndVal, eciToStage x = s := by
  exact
    otm_companion_reentry_fixed_iff_target_of_transport
      (s := s) (P := fun t => ∃ x : IndVal, eciToStage x = t)
      (genesis_companion_transport_closed_iff_eci_image (s := s))

theorem otm_companion_latent_reclassifies_to_autonomous :
    ((otmCompanionReclassify ReentryStage.latent : StageOmega) : ReentryStage) =
      ReentryStage.autonomous := by
  rw [coe_otmCompanionReclassify]
  rfl

theorem otm_companion_latent_not_reclassify_fixed :
    ((otmCompanionReclassify ReentryStage.latent : StageOmega) : ReentryStage) ≠
      ReentryStage.latent := by
  rw [coe_otmCompanionReclassify]
  decide

theorem otm_companion_not_every_stage_locally_closed :
    ¬ ∀ s : ReentryStage, OTMCompanionLocallyClosed s := by
  exact not_all_stages_are_closed

end HeytingLean.Varela
