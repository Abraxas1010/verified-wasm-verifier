import HeytingLean.Genesis.Life
import HeytingLean.Genesis.Glossary
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Genesis.CantorWitness

Phase-2 witness-space formalization:
- `EvalPath = Nat -> Bool`
- cardinality at continuum
- self-similarity via prefix-cylinder equivalence
- phase-history extraction from paths
-/

namespace HeytingLean.Genesis

open Cardinal

/-- An infinite binary evaluation path through the witness process. -/
abbrev EvalPath : Type := Nat → Bool

/-- Cantor-cut view of the same path space (glossary-compatible alias). -/
abbrev CantorCutPath : Type := EvalPath

/-- Canonical equivalence between Cantor-cut paths and completed observers. -/
def cantorCut_completedObserver_equiv : CantorCutPath ≃ CompletedObserver := Equiv.refl _

/-- Paths extending a fixed finite prefix. -/
def EvalPathFrom (pre : List Bool) : Type :=
  { p : EvalPath // ∀ i : Fin pre.length, p i = pre.get i }

/-- Prefix a path by a finite word. -/
def withPrefix (pre : List Bool) (p : EvalPath) : EvalPath :=
  fun n => if h : n < pre.length then pre.get ⟨n, h⟩ else p (n - pre.length)

/-- Canonical embedding from unrestricted paths into a fixed prefix cylinder. -/
def attachPrefix (pre : List Bool) (p : EvalPath) : EvalPathFrom pre := by
  refine ⟨withPrefix pre p, ?_⟩
  intro i
  simp [withPrefix, i.is_lt]

/-- Forget the finite prefix and keep the infinite tail. -/
def dropPrefix (pre : List Bool) (p : EvalPathFrom pre) : EvalPath :=
  fun n => p.1 (n + pre.length)

/-- Evaluation tree self-similarity: every prefix cylinder is equivalent to the whole space. -/
def evalTreeSelfSimilar (pre : List Bool) : EvalPathFrom pre ≃ EvalPath where
  toFun := dropPrefix pre
  invFun := attachPrefix pre
  left_inv := by
    intro p
    apply Subtype.ext
    funext n
    by_cases h : n < pre.length
    · have hfix : p.1 n = pre.get ⟨n, h⟩ := p.2 ⟨n, h⟩
      simp [attachPrefix, withPrefix, h, hfix]
    · have hge : pre.length ≤ n := Nat.le_of_not_gt h
      have hsum : n - pre.length + pre.length = n := Nat.sub_add_cancel hge
      simp [dropPrefix, attachPrefix, withPrefix, h, hsum]
  right_inv := by
    intro p
    funext n
    have hnot : ¬ n + pre.length < pre.length := by
      exact Nat.not_lt.mpr (Nat.le_add_left _ _)
    simp [dropPrefix, attachPrefix, withPrefix, hnot]

def eval_tree_self_similar (pre : List Bool) : EvalPathFrom pre ≃ EvalPath :=
  evalTreeSelfSimilar pre

/-- Cardinality result for evaluation paths. -/
theorem evalPath_card : #EvalPath = Cardinal.continuum := by
  simp [EvalPath]

/-- Every prefix cylinder has continuum cardinality. -/
theorem evalPathFrom_card (pre : List Bool) : #(EvalPathFrom pre) = Cardinal.continuum := by
  simpa using (Cardinal.mk_congr (evalTreeSelfSimilar pre)).trans evalPath_card

/-- Pointwise phase history induced by a path. -/
def phaseSequence (p : EvalPath) : Nat → Iterant Bool :=
  fun n => evalLife (p n)

theorem path_determines_phases (p : EvalPath) :
    ∀ n, phaseSequence p n = if p n then phaseJ else phaseI := by
  intro n
  rfl

theorem evalLife_injective : Function.Injective evalLife := by
  intro b₁ b₂ h
  cases b₁ <;> cases b₂
  · rfl
  · exfalso
    exact phaseI_ne_phaseJ h
  · exfalso
    exact phaseI_ne_phaseJ h.symm
  · rfl

theorem paths_distinguish {p q : EvalPath} (h : p ≠ q) :
    ∃ n, phaseSequence p n ≠ phaseSequence q n := by
  by_contra hno
  have hphase : phaseSequence p = phaseSequence q := by
    funext n
    by_contra hn
    exact hno ⟨n, hn⟩
  apply h
  funext n
  exact evalLife_injective (congrArg (fun f => f n) hphase)

end HeytingLean.Genesis
