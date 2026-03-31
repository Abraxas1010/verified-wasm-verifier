import HeytingLean.Genesis

/-!
# Genesis Phase 13 Sanity

Deferred-closure checks for:
- level > 1 transfinite tower growth,
- Cantor-cut topological homeomorphism lane.
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open Cardinal

#check LevelPaths
#check Level2Paths
#check levelPaths_card_succ
#check level1_lt_level2
#check evalPath_prefix_homeomorph
#check cantorCut_homeomorph_transport_ready
#check evalPath_to_ternaryCantor
#check evalPath_to_ternaryCantor_mem_cantorSet
#check continuous_evalPath_to_ternaryCantor
#check evalPath_to_ternaryCantor_range_subset
#check evalPath_equiv_ternaryCantor_range
#check cantorCut_equiv_ternaryCantor_range
#check evalPath_to_ternaryCantor_homeomorph_range
#check evalPath_to_ternaryCantorSubtype_surjective
#check evalPath_to_ternaryCantor_surjective_on_cantorSet
#check evalPath_to_ternaryCantor_homeomorph_cantorSubtype
#check prefix_homeomorph_image_mem_cantorSet
#check cantorSet_not_countable
#check exists_continuous_injective_evalPath_to_cantorSet
#check exists_continuous_injective_evalPath_to_cantorSubtype
#check exists_continuous_evalPath_embedding_into_cantorSubtype

def pTrue : EvalPath := fun _ => true
def pPrefNil : EvalPathFrom [] := attachPrefix [] pTrue

example : #Level2Paths = 2 ^ #Level1Paths := by
  exact level2_paths_cardinality

example : #Level1Paths < #Level2Paths := by
  exact level1_lt_level2

example : eventualStabilizes (prefix_homeomorph_to_witnessInterior [] pPrefNil 0).source := by
  exact (cantorCut_homeomorph_transport_ready [] pPrefNil 0).2 (by
    change (dropPrefix [] (attachPrefix [] pTrue)) 0 = true
    simp [dropPrefix, attachPrefix, withPrefix, pTrue])

example : (evalPath_equiv_ternaryCantor_range pTrue).1 ∈ cantorSet := by
  simpa [evalPath_equiv_ternaryCantor_range_apply] using
    (evalPath_to_ternaryCantor_mem_cantorSet pTrue)

example : evalPath_to_ternaryCantor (evalPath_prefix_homeomorph [] pPrefNil) ∈ cantorSet := by
  simpa using prefix_homeomorph_image_mem_cantorSet [] pPrefNil

example : ¬ (cantorSet : Set ℝ).Countable := by
  exact cantorSet_not_countable

example : ∃ g : (ℕ → Bool) → {x : ℝ // x ∈ cantorSet}, Continuous g ∧ Function.Injective g := by
  exact exists_continuous_injective_evalPath_to_cantorSubtype

example : Function.Surjective evalPath_to_ternaryCantorSubtype := by
  exact evalPath_to_ternaryCantorSubtype_surjective

end HeytingLean.Tests.Genesis
