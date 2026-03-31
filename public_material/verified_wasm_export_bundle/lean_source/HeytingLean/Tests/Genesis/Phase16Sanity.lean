import HeytingLean.Genesis

/-!
# Genesis Phase 16 Sanity

Euler-angle canonical triple and Bloch correspondence checks.
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open HeytingLean.Ontology

#check euler_bloch_equiv
#check eulerCirclePhases
#check euler_circle_phase_model
#check orthogonal_triple_consistency
#check iterant_matrix_to_bloch

/-- Canonical Bloch state along +x axis. -/
def blochX : BlochState :=
  { x := 1
    y := 0
    z := 0
    norm_one := by norm_num }

/-- Euler triple obtained canonically from `blochX`. -/
noncomputable def eulerX : EulerTriple :=
  fromBloch blochX

example : toBloch eulerX = blochX := by
  simpa [eulerX] using toBloch_fromBloch blochX

example : fromBloch (toBloch eulerX) = eulerX := by
  simpa [eulerX] using fromBloch_toBloch eulerX

example : eulerPauliObservable eulerX = blochPauliObservable (toBloch eulerX) := by
  simpa [eulerX] using iterant_matrix_to_bloch eulerX

example : eulerCirclePhases eulerX =
    (primordialOscillation eulerX.θx, primordialOscillation eulerX.θy, primordialOscillation eulerX.θz) := by
  exact euler_circle_phase_model eulerX

example : (toBloch eulerX).x ^ 2 + (toBloch eulerX).y ^ 2 + (toBloch eulerX).z ^ 2 = 1 := by
  exact orthogonal_triple_consistency eulerX

example :
    primordialOscillation (eulerX.θx + Real.pi) = -primordialOscillation eulerX.θx := by
  exact euler_circle_antiphase_x eulerX

end HeytingLean.Tests.Genesis
