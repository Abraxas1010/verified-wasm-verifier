import HeytingLean.Epistemic.Occam
import HeytingLean.Meta.AIT.Prefix
import HeytingLean.Meta.AIT.OccamDemocracy
import HeytingLean.Generative.IntNucleusKit

/-
# Bridging code-length complexity and birth index

This module provides a small definitional bridge between:

* the algorithmic complexity of a model code, measured by
  `codeLength : Program → Nat`, and
* the emergent complexity of an Ωᴿ-element, measured by the
  `birth` index of a reentry nucleus `R` from `HeytingLean.Epistemic.Occam`.

	The intent is not to assert new theorems yet, but to give a precise
	shape to objects that carry both notions of complexity so that later
	phases can state and prove comparison results without introducing
	extra axioms.
	-/

namespace HeytingLean.Meta.AIT

open HeytingLean.Epistemic
open HeytingLean.LoF
open HeytingLean.Generative

variable {α M D O : Type} [PrimaryAlgebra α]

/-- A reentry-based model family: combines a reentry nucleus `R`,
a democratic model family `family`, and an interpretation map from
models to Ωᴿ-level elements. -/
structure ReentryModelFamily where
  R        : Reentry α
  family   : ModelFamily M D O
  interpret : M → α

namespace ReentryModelFamily

variable (F : ReentryModelFamily (α := α) (M := M) (D := D) (O := O))

/-- Code-based complexity of a model: the length of its program. -/
def codeComplexity (m : M) : Nat :=
  codeLength (F.family.code m)

/-- Birth-based complexity of a model: the birth index of its Ωᴿ-level
interpretation under the nucleus `R`. -/
noncomputable def birthComplexity (m : M) : Nat :=
  birth F.R (F.interpret m)

/-- If a model's interpreted element is fixed by `R`, its birth-based
complexity is zero. This follows directly from the existing lemma
`birth_eq_zero_of_fixed`. -/
lemma birthComplexity_eq_zero_of_fixed {m : M}
    (h : F.R (F.interpret m) = F.interpret m) :
    F.birthComplexity m = 0 := by
  unfold birthComplexity
  simpa using
    (birth_eq_zero_of_fixed (R := F.R) (a := F.interpret m) h)

/-- Trivial comparison: if a model's interpreted element is fixed by `R`,
then its birth-based complexity (which is `0` in this case) is bounded
above by its code-based complexity. This is a first, fully general
inequality relating the two measures. -/
lemma birthComplexity_le_codeComplexity_of_fixed {m : M}
    (h : F.R (F.interpret m) = F.interpret m) :
    F.birthComplexity m ≤ F.codeComplexity m := by
  have hz : F.birthComplexity m = 0 :=
    F.birthComplexity_eq_zero_of_fixed (m := m) h
  have h0 : 0 ≤ F.codeComplexity m := Nat.zero_le _
  simpa [codeComplexity, hz] using h0

end ReentryModelFamily

/-- An interior-reentry-based model family: combines an interior nucleus `R`,
its democratic model family `family`, and an interpretation map from models to
elements of the ambient primary algebra. This mirrors `ReentryModelFamily`
but uses the interior-style `IntReentry` and the corresponding `ibirth`. -/
structure IntReentryModelFamily where
  R        : IntReentry α
  family   : ModelFamily M D O
  interpret : M → α

namespace IntReentryModelFamily

variable (F : IntReentryModelFamily (α := α) (M := M) (D := D) (O := O))

/-- Code-based complexity in the interior setting: the length of the model
code, identical to the reentry-based notion. -/
def codeComplexity (m : M) : Nat :=
  codeLength (F.family.code m)

/-- Birth-based complexity for an interior nucleus: the minimal number of
interior breaths (`ibirth`) needed for the interpretation of `m` to
stabilise under `R`. -/
noncomputable def birthComplexity (m : M) : Nat :=
  IntNucleusKit.ibirth (R := F.R) (F.interpret m)

/-- If the interpretation of `m` is a fixed point of the interior nucleus,
its interior birth complexity is zero. -/
lemma birthComplexity_eq_zero_of_fixed {m : M}
    (h : F.R (F.interpret m) = F.interpret m) :
    F.birthComplexity m = 0 := by
  unfold birthComplexity
  simpa using
    IntNucleusKit.ibirth_eq_zero_of_fixed
      (R := F.R) (a := F.interpret m) h

/-- For any model in an interior reentry family, the birth complexity is
bounded above by `1`. This is a direct consequence of the generic
`ibirth_le_one` lemma for interior nuclei. -/
lemma birthComplexity_le_one (m : M) :
    F.birthComplexity m ≤ 1 := by
  unfold birthComplexity
  simpa using
    IntNucleusKit.ibirth_le_one
      (R := F.R) (a := F.interpret m)

end IntReentryModelFamily

end HeytingLean.Meta.AIT
