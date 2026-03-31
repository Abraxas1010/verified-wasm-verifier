import HeytingLean.Varela

namespace HeytingLean.Tests.Varela

open HeytingLean.Varela
open HeytingLean.ClosingTheLoop.MR
open HeytingLean.LoF.MRSystems
open IndVal
open ReentryStage

example : cross .autonomous = .autonomous := rfl

example : crossWave waveI = waveJ := cross_waveI_eq_waveJ

example : Diamond.cross Diamond.i = Diamond.i := rfl

example : stageClosure .latent = .autonomous := rfl

example : stageToECI (eciToOmega .marked) = .marked := rfl

example :
    ReentryStage.autonomous ∈ (stageNucleus.toSublocale : Set ReentryStage) := by
  rw [mem_stageOmega_iff_stageClosure_fixed]
  rfl

example :
    ReentryStage.unmarked ∈ (stageNucleus.toSublocale : Set ReentryStage) ↔
      ∃ x : IndVal, eciToStage x = ReentryStage.unmarked := by
  exact mem_stageOmega_iff_eci_image

example {s : ReentryStage} :
    stageClosure s = s ↔ s ∈ (stageNucleus.toSublocale : Set ReentryStage) := by
  exact transport_reentry_fixed_iff_stageClosed

example {s : ReentryStage} :
    stageClosure s = s ↔ StageClosed s := by
  exact exemplar_reentry_fixed_iff_stage_closed

example {s : ReentryStage} :
    StageClosed s ↔ ∃ x : IndVal, eciToStage x = s := by
  exact exemplar_stage_closed_iff_eci_image

example {s : ReentryStage} :
    GenesisCompanionStabilizes s ↔ GenesisCompanionClosed s := by
  exact genesis_companion_transport_compat_with_stabilization

example {s : ReentryStage} :
    GenesisCompanionClosed s ↔ ∃ x : IndVal, eciToStage x = s := by
  exact genesis_companion_transport_closed_iff_eci_image

example :
    ReentryStage.latent ∉ (stageNucleus.toSublocale : Set ReentryStage) := by
  exact latent_not_stageClosed

example :
    ¬ ∀ s : ReentryStage, stageClosure s = s := by
  exact not_all_stages_are_fixed

example :
    ¬ ∀ s : ReentryStage, StageClosed s := by
  exact not_all_stages_are_closed

example :
    ¬ ∀ s : ReentryStage, ∃ x : IndVal, eciToStage x = s := by
  exact not_every_stage_has_eci_preimage

example :
    ¬ ∀ s : ReentryStage, GenesisCompanionStabilizes s := by
  exact genesis_companion_not_every_stage_stabilizes

example :
    ¬ ∀ s : ReentryStage, GenesisCompanionClosed s := by
  exact genesis_companion_not_every_stage_closed

example :
    stageClosure ReentryStage.latent ≠ ReentryStage.latent := by
  decide

example :
    ambientStages = [.unmarked, .latent, .autonomous, .marked] := rfl

example :
    ambientClosureImage = [.unmarked, .autonomous, .autonomous, .marked] := by
  exact ambientClosureImage_eq

example :
    fixedStages = [.unmarked, .autonomous, .marked] := rfl

example :
    eciImageStages = [.unmarked, .autonomous, .marked] := rfl

example :
    fixedStages = eciImageStages := by
  exact fixedStages_eq_eciImageStages

example (s : ReentryStage) :
    s ∈ ambientStages := by
  exact mem_ambientStages s

example {s : ReentryStage} :
    s ∈ fixedStages ↔ stageClosure s = s := by
  exact mem_fixedStages_iff

example {s : ReentryStage} :
    s ∈ closedStages ↔ StageClosed s := by
  exact mem_closedStages_iff

example {s : ReentryStage} :
    s ∈ eciImageStages ↔ ∃ x : IndVal, eciToStage x = s := by
  exact mem_eciImageStages_iff

example (s : StageOmega) :
    eciToOmega (stageToECI s) = s := by
  exact transport_stageOmega_to_eci s

example (x : IndVal) :
    stageToECI (eciToOmega x) = x := by
  exact transport_eci_to_stageOmega x

example (a b : StageOmega) :
    stageToECI a ≤ stageToECI b ↔ a ≤ b := by
  exact transport_stageClosed_order_reflects

example : omegaOrderIsoECI (eciToOmega .autonomous) = .autonomous := rfl

example : omegaOrderIsoECI.symm .marked = eciToOmega .marked := rfl

example : exemplar_stageOmega_order_iso (eciToOmega .marked) = .marked := rfl

example (a b : StageOmega) :
    stageToECI (a ⊔ b) = stageToECI a ⊔ stageToECI b := by
  exact stageToECI_sup a b

example {s : ReentryStage} :
    stageClosure s = s ↔ ((otmCompanionReclassify s : StageOmega) : ReentryStage) = s := by
  exact otm_companion_reentry_fixed_iff_reclassify_fixed

example {s : ReentryStage} :
    stageClosure s = s ↔ OTMCompanionLocallyClosed s := by
  exact otm_companion_reentry_fixed_iff_local_closed

example :
    ((otmCompanionReclassify ReentryStage.latent : StageOmega) : ReentryStage) =
      ReentryStage.autonomous := by
  exact otm_companion_latent_reclassifies_to_autonomous

example :
    ((otmCompanionReclassify ReentryStage.latent : StageOmega) : ReentryStage) ≠
      ReentryStage.latent := by
  exact otm_companion_latent_not_reclassify_fixed

example {S : MRSystem} {b : S.B} (RI : RightInverseAt S b) (Φ : Selector S) :
    closeSelector S b RI (closeSelector S b RI Φ) = closeSelector S b RI Φ := by
  exact closeSelector_idempotent (S := S) (b := b) RI Φ

example {S : MRSystem} {b : S.B} (RI : RightInverseAt S b)
    (U : Set (Selector S)) :
    SemanticClosureNucleus (S := S) b RI U = U ↔
      nonClosedCore (S := S) (b := b) RI ⊆ U := by
  exact semantic_closure_fixed_iff (S := S) (b := b) RI U

example : ¬ (eciToOmega .autonomous ⊔ (eciToOmega .autonomous)ᶜ = (⊤ : StageOmega)) := by
  exact omega_autonomous_not_classical

example : ¬ (eciToOmega .autonomous ⊔ (eciToOmega .autonomous)ᶜ = (⊤ : StageOmega)) := by
  exact autonomous_point_remains_nonclassical

example :
    stageClosure ReentryStage.autonomous = ReentryStage.autonomous := by
  exact target_varela_autonomous_fixed

example :
    StageClosed ReentryStage.marked := by
  exact target_varela_marked_closed

example :
    ∃ x : IndVal, eciToStage x = ReentryStage.marked := by
  exact target_varela_marked_eci_image

example :
    GenesisCompanionClosed ReentryStage.autonomous := by
  exact target_varela_genesis_autonomous_closed

example :
    ¬ ∀ s : ReentryStage, StageClosed s := by
  exact target_varela_not_all_stages_closed

example :
    ((otmCompanionReclassify ReentryStage.latent : StageOmega) : ReentryStage) =
      ReentryStage.autonomous := by
  exact target_varela_otm_latent_reclassifies_to_autonomous

example :
    ((otmCompanionReclassify ReentryStage.latent : StageOmega) : ReentryStage) ≠
      ReentryStage.latent := by
  exact target_varela_latent_not_reclassify_fixed

example :
    ¬ (eciToOmega .autonomous ⊔ (eciToOmega .autonomous)ᶜ = (⊤ : StageOmega)) := by
  exact target_varela_autonomous_not_classical

end HeytingLean.Tests.Varela
