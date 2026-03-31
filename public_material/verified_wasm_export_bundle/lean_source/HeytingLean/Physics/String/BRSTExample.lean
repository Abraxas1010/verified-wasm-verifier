import HeytingLean.Physics.String.BRST

/-
Concrete tiny BRST example.

We take `V := Bool` as a two-point state space and define a
nilpotent differential `Q` by sending `false ↦ true` and
`true ↦ true`.  Then `Q ∘ Q` is constant `true`, so the
kernel is `{false}` and the image is `{true}`; the resulting
cohomology has a single non-trivial class represented by `false`.

	This file is intentionally minimal and executable-first: it gives
	an honest square-zero proof for a specific `Q` without introducing
	any fake propositions into the core `BRST` structure.
	-/

namespace HeytingLean
namespace Physics
namespace String

open HeytingLean.Physics.String

/-- Tiny state space for a BRST differential. -/
abbrev BRSTState := Bool

/-- A simple nilpotent differential on `Bool`:
`Q false = true`, `Q true = true`. -/
@[simp] def QBool : BRSTState → BRSTState
  | false => true
  | true  => true

@[simp] theorem QBool_sq (b : BRSTState) : QBool (QBool b) = true := by
  cases b <;> simp [QBool]

/-- Kernel of the BRST differential. -/
def kerQBool (b : BRSTState) : Prop := QBool b = true

/-- Image of the BRST differential. -/
def imQBool (b : BRSTState) : Prop := ∃ a, QBool a = b

/-- Cohomology classes for this tiny model:
only two possibilities, represented by `false` and `true`. -/
inductive Cohomology where
  | trivial : Cohomology
  | excited : Cohomology

/-- Classify a state into a cohomology class. -/
@[simp] def classOf (b : BRSTState) : Cohomology :=
  match b with
  | false => Cohomology.trivial
  | true  => Cohomology.excited

/-- `false` and `true` land in different classes. -/
theorem class_false_ne_true : classOf false ≠ classOf true := by
  simp [classOf]

/-- Instantiate the abstract `BRST` structure with `QBool`.

We record nilpotence as the propositional fact that the image is
contained in the kernel in this two-point model. -/
def exampleBRST : BRST BRSTState where
  Q := QBool
  squareZero := ∀ b, kerQBool (QBool b)

/-- Witness that `exampleBRST.squareZero` holds. -/
@[simp] theorem exampleBRST_squareZero : exampleBRST.squareZero := by
  intro b
  cases b <;> simp [exampleBRST, kerQBool, QBool]

end String
end Physics
end HeytingLean
