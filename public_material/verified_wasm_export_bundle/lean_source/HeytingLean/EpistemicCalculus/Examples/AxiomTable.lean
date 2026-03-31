import HeytingLean.EpistemicCalculus.Examples.PossibilityTheory
import HeytingLean.EpistemicCalculus.Examples.CertaintyFactors
import HeytingLean.EpistemicCalculus.Examples.BipolarPossibility
import HeytingLean.EpistemicCalculus.Examples.IntervalProbability

namespace HeytingLean.EpistemicCalculus.Examples

/-!
Concrete witness table for the core examples.
These are intentionally explicit so downstream modules can import a stable surface.
-/

noncomputable section

example : Optimistic PT := inferInstance
example : IdempotentFusion PT := inferInstance
example : Fallible PT := inferInstance

example : Closed CF := inferInstance
example : Fallible CF := inferInstance

example : Optimistic PTbi := inferInstance
example : IdempotentFusion PTbi := inferInstance
example : Fallible PTbi := inferInstance

example : Optimistic IP := inferInstance
example : IdempotentFusion IP := inferInstance
example : Fallible IP := inferInstance

def ptHalf : PT := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
def ptThreeTenths : PT := ⟨(3 / 10 : ℝ), by constructor <;> norm_num⟩

theorem pt_not_strongly_conservative :
    ¬ (∀ x y : PT, x ≤ x fus y) := by
  intro h
  have hbad := h ptHalf ptThreeTenths
  change (1 / 2 : ℝ) ≤ min (1 / 2 : ℝ) (3 / 10 : ℝ) at hbad
  norm_num at hbad

theorem pt_not_cancellative :
    ¬ (∀ x y z : PT, x fus z ≤ y fus z → x ≤ y) := by
  intro h
  let x : PT := ⟨(7 / 10 : ℝ), by constructor <;> norm_num⟩
  let y : PT := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  let z : PT := ⟨(3 / 10 : ℝ), by constructor <;> norm_num⟩
  have hz : x fus z ≤ y fus z := by
    change min (7 / 10 : ℝ) (3 / 10 : ℝ) ≤ min (1 / 2 : ℝ) (3 / 10 : ℝ)
    norm_num
  have hxy : x ≤ y := h x y z hz
  change (7 / 10 : ℝ) ≤ (1 / 2 : ℝ) at hxy
  norm_num at hxy

end

end HeytingLean.EpistemicCalculus.Examples
