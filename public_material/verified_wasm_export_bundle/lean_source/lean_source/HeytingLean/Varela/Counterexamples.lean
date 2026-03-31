import HeytingLean.Varela.BridgeExemplar

/-!
# Varela Counterexamples

This file turns the Varela finite witness into an explicit small-model refutation
surface. The point is not merely to support positive transport language, but to expose
the exact ambient claims that fail when made too strong.
-/

namespace HeytingLean.Varela

/-- The latent stage is not a fixed point of the ambient closure. -/
theorem latent_not_fixed :
    stageClosure ReentryStage.latent ≠ ReentryStage.latent := by
  decide

/-- Not every ambient stage is fixed by the closure. -/
theorem not_all_stages_are_fixed :
    ¬ ∀ s : ReentryStage, stageClosure s = s := by
  intro h
  exact latent_not_fixed (h ReentryStage.latent)

/-- Not every ambient stage lies in the closed witness part. -/
theorem not_all_stages_are_closed :
    ¬ ∀ s : ReentryStage, StageClosed s := by
  intro h
  exact latent_not_stageClosed (h ReentryStage.latent)

/-- The latent stage witnesses failure of full ambient ECI-image coverage. -/
theorem latent_not_eci_image :
    ¬ ∃ x : IndVal, eciToStage x = ReentryStage.latent := by
  intro hx
  have hfixed :
      stageClosure ReentryStage.latent = ReentryStage.latent :=
    (exemplar_reentry_fixed_iff_eci_image (s := ReentryStage.latent)).2 hx
  exact latent_not_fixed hfixed

/-- The ambient carrier contains a genuinely non-fixed point. -/
theorem exists_nonfixed_stage :
    ∃ s : ReentryStage, stageClosure s ≠ s := by
  exact ⟨ReentryStage.latent, latent_not_fixed⟩

/-- The ambient carrier contains a genuinely non-closed point. -/
theorem exists_unclosed_stage :
    ∃ s : ReentryStage, ¬ StageClosed s := by
  exact ⟨ReentryStage.latent, latent_not_stageClosed⟩

/-- The finite witness does not support the over-strong claim that every stage has an ECI preimage. -/
theorem not_every_stage_has_eci_preimage :
    ¬ ∀ s : ReentryStage, ∃ x : IndVal, eciToStage x = s := by
  intro h
  exact latent_not_eci_image (h ReentryStage.latent)

/-- The autonomous closed point still exhibits the nonclassical complement behavior. -/
theorem autonomous_point_remains_nonclassical :
    ¬ (eciToOmega .autonomous ⊔ (eciToOmega .autonomous)ᶜ = (⊤ : StageOmega)) := by
  exact omega_autonomous_not_classical

end HeytingLean.Varela
