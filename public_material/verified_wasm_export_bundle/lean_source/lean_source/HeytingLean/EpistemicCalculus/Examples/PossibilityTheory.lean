import HeytingLean.EpistemicCalculus.Basic
import HeytingLean.EpistemicCalculus.Axioms
import Mathlib.Topology.UnitInterval

namespace HeytingLean.EpistemicCalculus.Examples

/-- Possibility theory carrier `[0,1]`. -/
abbrev PT := Set.Icc (0 : ℝ) 1

def ptZero : PT := ⟨0, by constructor <;> norm_num⟩
def ptOne : PT := ⟨1, by constructor <;> norm_num⟩

def ptFusion (x y : PT) : PT := by
  refine ⟨min x.1 y.1, ?_⟩
  constructor
  · exact le_min x.2.1 y.2.1
  · exact le_trans (min_le_left _ _) x.2.2

instance : EpistemicCalculus PT where
  fusion := ptFusion
  unit := ptOne
  fusion_assoc := by
    intro x y z
    apply Subtype.ext
    simp [ptFusion, min_assoc]
  fusion_comm := by
    intro x y
    apply Subtype.ext
    simp [ptFusion, min_comm]
  fusion_unit_left := by
    intro x
    apply Subtype.ext
    change min 1 x.1 = x.1
    exact min_eq_right x.2.2
  fusion_mono := by
    intro x x' y y' hx hy
    exact min_le_min hx hy
  nontrivial := by
    refine ⟨ptZero, ptOne, ?_⟩
    intro h
    have hval : (ptZero : ℝ) = (ptOne : ℝ) := congrArg Subtype.val h
    norm_num [ptZero, ptOne] at hval

instance : Optimistic PT where
  top := ptOne
  le_top := by
    intro x
    exact x.2.2

instance : IdempotentFusion PT where
  idem := by
    intro x
    apply Subtype.ext
    change min x.1 x.1 = x.1
    exact min_eq_left le_rfl

instance : Fallible PT where
  revisable := by
    intro x y
    refine ⟨y, ?_⟩
    change min x.1 y.1 ≤ y.1
    exact min_le_right _ _

end HeytingLean.EpistemicCalculus.Examples
