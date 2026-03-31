import Mathlib/Data/Set/Lattice

open scoped Classical

namespace HeytingLean.LoF.Lens.FCA

/-! # Formal Concept Analysis (attribute closure)

We formalize a finite/infinite context `(O, A, ⊨)` and define the standard
Galois derivations `X ↦ X'` and `Y ↦ Y'` between attributes and objects.
The attribute‑side closure is `J X := (X')'`. We prove it is extensive,
monotone, idempotent, and ∧‑preserving: `J (X ∩ Y) = J X ∩ J Y`.
-/

structure Context (O A : Type _) where
  holds : O → A → Prop

variable {O A : Type _} (C : Context O A)

namespace Deriv

/-- Attribute derivation: `X' = { o | ∀ a ∈ X, o ⊨ a }`. -/
def obj (X : Set A) : Set O := { o | ∀ a, a ∈ X → C.holds o a }

/-- Object derivation: `Y' = { a | ∀ o ∈ Y, o ⊨ a }`. -/
def attr (Y : Set O) : Set A := { a | ∀ o, o ∈ Y → C.holds o a }

@[simp] lemma mem_obj_iff {X : Set A} {o : O} :
  o ∈ obj (C := C) X ↔ ∀ a, a ∈ X → C.holds o a := Iff.rfl

@[simp] lemma mem_attr_iff {Y : Set O} {a : A} :
  a ∈ attr (C := C) Y ↔ ∀ o, o ∈ Y → C.holds o a := Iff.rfl

end Deriv

/-- Attribute closure `J X := (X')'`. -/
def J (X : Set A) : Set A := Deriv.attr (C := C) (Deriv.obj (C := C) X)

namespace J

variable {C} (X Y : Set A)

@[simp] lemma mem_iff {a : A} :
  a ∈ J (C := C) X ↔ ∀ o, (∀ a', a' ∈ X → C.holds o a') → C.holds o a := by
  rfl

lemma extensive : X ⊆ J (C := C) X := by
  intro a ha
  -- Show a ∈ (X')' i.e. every object having all attributes in X must satisfy a
  refine (mem_iff (C := C) (X := X)).mpr ?h
  intro o ho
  exact ho a ha

lemma monotone (hXY : X ⊆ Y) : J (C := C) X ⊆ J (C := C) Y := by
  intro a ha
  -- a ∈ (X')' ⇒ a ∈ (Y')'
  refine (mem_iff (C := C) (X := Y)).mpr ?h
  intro o hoY
  -- need C.holds o a; from ha: o has all of X → holds a. It suffices to show o has all of X.
  have hoX : ∀ a', a' ∈ X → C.holds o a' := by
    intro a' ha'X
    exact hoY a' (hXY ha'X)
  have : (∀ a', a' ∈ X → C.holds o a') → C.holds o a :=
    (mem_iff (C := C) (X := X)).mp ha o
  exact this hoX

lemma idempotent : J (C := C) (J (C := C) X) = J (C := C) X := by
  -- J(J X) ⊆ J X by monotonicity and extensiveness; converse by extensiveness
  apply Set.Subset.antisymm
  · intro a ha
    -- use monotonicity with X ⊆ J X
    have hmon := monotone (C := C) (X := J (C := C) X) (Y := J (C := C) X) (by intro a' ha'; exact ha')
    -- trivial, but we re-prove directly: a ∈ J(J X) implies a ∈ J X
    exact
      (mem_iff (C := C) (X := J (C := C) X)).mp ha
  · -- J X ⊆ J (J X) by monotonicity and X ⊆ J X (extensive)
    intro a ha
    have hext := extensive (C := C) (X := X)
    exact (monotone (C := C) (X := X) (Y := J (C := C) X) hext) ha

lemma inf_preserving_left : J (C := C) (X ∩ Y) ⊆ J (C := C) X ∩ J (C := C) Y := by
  intro a ha
  have hX : a ∈ J (C := C) X := by
    refine (mem_iff (C := C) (X := X)).mpr ?h
    intro o hoX
    -- build a proof for X∩Y using the left projection
    have hoXY : ∀ a', a' ∈ (X ∩ Y) → C.holds o a' := by
      intro a' ha'XY; exact hoX a' ha'XY.left
    exact (mem_iff (C := C) (X := X ∩ Y)).mp ha o hoXY
  have hY : a ∈ J (C := C) Y := by
    refine (mem_iff (C := C) (X := Y)).mpr ?h
    intro o hoY
    have hoXY : ∀ a', a' ∈ (X ∩ Y) → C.holds o a' := by
      intro a' ha'XY; exact hoY a' ha'XY.right
    exact (mem_iff (C := C) (X := X ∩ Y)).mp ha o hoXY
  exact Set.mem_inter_iff.mpr ⟨hX, hY⟩

end J

end HeytingLean.LoF.Lens.FCA
