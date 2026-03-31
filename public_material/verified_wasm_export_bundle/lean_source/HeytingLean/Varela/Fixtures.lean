import HeytingLean.Varela.Counterexamples

/-!
# Varela Fixtures

Deterministic finite enumerations for the ambient stage carrier and its fixed/closed
subsurfaces. These are intentionally explicit so they can be reused in tests and ATP
fixtures without re-deriving list content each time.
-/

namespace HeytingLean.Varela

open ReentryStage

def ambientStages : List ReentryStage :=
  [.unmarked, .latent, .autonomous, .marked]

def ambientClosureImage : List ReentryStage :=
  ambientStages.map stageClosure

def fixedStages : List ReentryStage :=
  [.unmarked, .autonomous, .marked]

def closedStages : List ReentryStage :=
  fixedStages

def eciImageStages : List ReentryStage :=
  [.unmarked, .autonomous, .marked]

theorem ambientClosureImage_eq :
    ambientClosureImage = [.unmarked, .autonomous, .autonomous, .marked] := rfl

theorem fixedStages_eq_eciImageStages :
    fixedStages = eciImageStages := rfl

theorem mem_ambientStages (s : ReentryStage) :
    s ∈ ambientStages := by
  cases s <;> simp [ambientStages]

theorem mem_fixedStages_iff {s : ReentryStage} :
    s ∈ fixedStages ↔ stageClosure s = s := by
  cases s <;> simp [fixedStages, stageClosure]

theorem mem_closedStages_iff {s : ReentryStage} :
    s ∈ closedStages ↔ StageClosed s := by
  rw [closedStages, mem_fixedStages_iff]
  exact exemplar_reentry_fixed_iff_stage_closed

theorem mem_eciImageStages_iff {s : ReentryStage} :
    s ∈ eciImageStages ↔ ∃ x : IndVal, eciToStage x = s := by
  rw [← fixedStages_eq_eciImageStages, mem_fixedStages_iff]
  exact exemplar_reentry_fixed_iff_eci_image

end HeytingLean.Varela
