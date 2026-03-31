import Mathlib.Order.Closure
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

namespace HeytingLean
namespace Topos

open CategoryTheory

universe u v

variable (C : Type u) [Category.{v} C] [CategoryTheory.Limits.HasPullbacks C]

/--
`LocalOperator C` is a **universal closure operator** on subobjects:

it consists of a closure operator on each `Subobject X`, stable under pullback.

This is the “subobject-lattice” presentation of a Lawvere–Tierney modality.  A full
classifier-based presentation (endomorphism `j : Ω ⟶ Ω` plus axioms) lives separately
in `HeytingLean.Topos.LTfromNucleus`.
-/
structure LocalOperator where
  cl : ∀ X : C, ClosureOperator (Subobject X)
  pullback_stable :
    ∀ {X Y : C} (f : Y ⟶ X) (S : Subobject X),
      (Subobject.pullback f).obj ((cl X) S) = (cl Y) ((Subobject.pullback f).obj S)

namespace LocalOperator

variable {C}

/-- A subobject is `closed` for a given LocalOperator when it is a fixed point. -/
def IsClosed (J : LocalOperator C) {X : C} (S : Subobject X) : Prop :=
  J.cl X S = S

@[simp] lemma isClosed_fixed (J : LocalOperator C) {X : C} (S : Subobject X) :
    IsClosed J S ↔ J.cl X S = S := Iff.rfl

/-- Extra (optional) structure: a local operator whose closure preserves binary infimum. -/
structure MeetPreserving (J : LocalOperator C) : Prop where
  /-- Closure commutes with intersection: `cl (S ⊓ T) = cl S ⊓ cl T`. -/
  map_inf : ∀ {X : C} (S T : Subobject X), J.cl X (S ⊓ T) = J.cl X S ⊓ J.cl X T

/-- Closed subobjects are stable under pullback for a `LocalOperator`. -/
lemma isClosed_pullback
    (J : LocalOperator C) {X Y : C} (f : Y ⟶ X) (S : Subobject X)
    (hS : IsClosed J S) :
    IsClosed J ((Subobject.pullback f).obj S) := by
  -- Use the stability equality and rewrite with closedness at `S`.
  dsimp [IsClosed]
  -- First, transport along the stability equality
  have h₁ : J.cl Y ((Subobject.pullback f).obj S)
      = (Subobject.pullback f).obj (J.cl X S) := by
    simpa using (J.pullback_stable f S).symm
  -- Then, use closedness at S to simplify the RHS
  have h₂ : (Subobject.pullback f).obj (J.cl X S)
      = (Subobject.pullback f).obj S := by
    have : (J.cl X S) = S := by simpa [IsClosed] using hS
    simpa using congrArg (fun T => (Subobject.pullback f).obj T) this
  exact h₁.trans h₂

end LocalOperator

end Topos
end HeytingLean
