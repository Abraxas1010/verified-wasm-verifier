import HeytingLean.EpistemicCalculus.Basic
import HeytingLean.EpistemicCalculus.Axioms
import Mathlib.Topology.UnitInterval

namespace HeytingLean.EpistemicCalculus.Examples

abbrev UnitI := Set.Icc (0 : ℝ) 1

/--
`PTbi`: bipolar possibility values as lower/upper confidence bounds.
Inconsistent pairs (`lo > hi`) are allowed and interpreted as contradictory states.
-/
structure PTbi where
  lo : UnitI
  hi : UnitI

@[ext] theorem PTbi.ext {a b : PTbi} (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) : a = b := by
  cases a
  cases b
  cases hlo
  cases hhi
  rfl

instance : LE PTbi where
  le a b := b.lo.1 ≤ a.lo.1 ∧ a.hi.1 ≤ b.hi.1

instance : PartialOrder PTbi where
  le := (· ≤ ·)
  le_refl a := ⟨le_rfl, le_rfl⟩
  le_trans a b c hab hbc := ⟨le_trans hbc.1 hab.1, le_trans hab.2 hbc.2⟩
  le_antisymm a b hab hba := by
    cases a with
    | mk alo ahi =>
      cases b with
      | mk blo bhi =>
        have hlo : alo = blo := by
          apply Subtype.ext
          exact le_antisymm hba.1 hab.1
        have hhi : ahi = bhi := by
          apply Subtype.ext
          exact le_antisymm hab.2 hba.2
        cases hlo
        cases hhi
        rfl

def ptbiUnit : PTbi where
  lo := ⟨0, by constructor <;> norm_num⟩
  hi := ⟨1, by constructor <;> norm_num⟩

def ptbiFusion (a b : PTbi) : PTbi where
  lo := ⟨max a.lo.1 b.lo.1, by
    constructor
    · exact le_trans a.lo.2.1 (le_max_left _ _)
    · exact max_le a.lo.2.2 b.lo.2.2⟩
  hi := ⟨min a.hi.1 b.hi.1, by
    constructor
    · exact le_min a.hi.2.1 b.hi.2.1
    · exact le_trans (min_le_left _ _) a.hi.2.2⟩

def ptbiInconsistent : PTbi where
  lo := ⟨1, by constructor <;> norm_num⟩
  hi := ⟨0, by constructor <;> norm_num⟩

instance : EpistemicCalculus PTbi where
  fusion := ptbiFusion
  unit := ptbiUnit
  fusion_assoc := by
    intro a b c
    ext <;> simp [ptbiFusion, max_assoc, min_assoc]
  fusion_comm := by
    intro a b
    ext <;> simp [ptbiFusion, max_comm, min_comm]
  fusion_unit_left := by
    intro a
    ext
    · change max (ptbiUnit.lo : ℝ) a.lo = a.lo
      exact max_eq_right a.lo.2.1
    · change min (ptbiUnit.hi : ℝ) a.hi = a.hi
      exact min_eq_right a.hi.2.2
  fusion_mono := by
    intro a a' b b' haa' hbb'
    refine ⟨?_, ?_⟩
    · exact max_le_max haa'.1 hbb'.1
    · exact min_le_min haa'.2 hbb'.2
  nontrivial := by
    refine ⟨ptbiUnit, ptbiInconsistent, ?_⟩
    intro h
    have hlo : (ptbiUnit.lo : ℝ) = (ptbiInconsistent.lo : ℝ) := congrArg (fun t => (t.lo : ℝ)) h
    norm_num [ptbiUnit, ptbiInconsistent] at hlo

instance : Optimistic PTbi where
  top := ptbiUnit
  le_top := by
    intro x
    change (ptbiUnit.lo : ℝ) ≤ x.lo ∧ x.hi ≤ (ptbiUnit.hi : ℝ)
    exact ⟨x.lo.2.1, x.hi.2.2⟩

instance : IdempotentFusion PTbi where
  idem := by
    intro x
    cases x with
    | mk lo hi =>
      apply PTbi.ext
      · apply Subtype.ext
        change max (lo : ℝ) lo = lo
        exact max_eq_left le_rfl
      · apply Subtype.ext
        change min (hi : ℝ) hi = hi
        exact min_eq_left le_rfl

instance : Fallible PTbi where
  revisable := by
    intro x y
    refine ⟨y, ?_⟩
    change (y.lo : ℝ) ≤ max x.lo y.lo ∧ min x.hi y.hi ≤ (y.hi : ℝ)
    exact ⟨le_max_right _ _, min_le_right _ _⟩

end HeytingLean.EpistemicCalculus.Examples
