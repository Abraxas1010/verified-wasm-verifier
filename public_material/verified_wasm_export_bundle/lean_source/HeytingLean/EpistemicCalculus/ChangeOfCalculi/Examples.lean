import HeytingLean.EpistemicCalculus.ChangeOfCalculi.Balanced
import HeytingLean.EpistemicCalculus.Examples.IntervalProbability
import HeytingLean.EpistemicCalculus.Examples.PossibilityTheory
import HeytingLean.EpistemicCalculus.Examples.CertaintyFactors

namespace HeytingLean.EpistemicCalculus.ChangeOfCalculi
namespace Examples

open HeytingLean.EpistemicCalculus.Examples

/-- Lemma 4.1 style bridge: corrected PTbi and IP are definitionally aligned. -/
def ptbiIsoIp : BalancedChange PTbi IP where
  map := id
  monotone := by intro x y h; exact h
  strict_monoidal := by intro x y; rfl
  strict_unit := rfl

/--
A concrete liberal map from PT to CF.

With the oplax-unit direction `map 𝟏 ≤ 𝟏`, monotonicity plus positivity in CF
forces a constant-at-unit witness in this PT→CF setting.
-/
def ptToCfMap (_x : PT) : CF := cfOne

theorem ptToCf_mono {x y : PT} (_h : x ≤ y) : ptToCfMap x ≤ ptToCfMap y := by
  simp [ptToCfMap]

theorem ptToCf_oplax (x y : PT) :
    ptToCfMap (x fus y) ≤ ptToCfMap x fus ptToCfMap y := by
  change (1 : ℝ) ≤ (1 : ℝ) * (1 : ℝ)
  norm_num

def ptToCfLiberal : LiberalChange PT CF where
  map := ptToCfMap
  monotone := by
    intro x y h
    exact ptToCf_mono h
  oplax_monoidal := by
    intro x y
    exact ptToCf_oplax x y
  oplax_unit := by
    change (1 : ℝ) ≤ (1 : ℝ)
    norm_num

end Examples
end HeytingLean.EpistemicCalculus.ChangeOfCalculi
