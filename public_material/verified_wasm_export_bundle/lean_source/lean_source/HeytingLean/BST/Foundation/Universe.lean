import Mathlib

/-!
# BST.Foundation.Universe

Core bounded-universe scaffolding for the first BST slice.

The universal finite bound is modeled as explicit data, never as a global axiom.
`BoundedFinset U α` is the basic bounded-set carrier used in the initial development.
-/

namespace HeytingLean.BST

structure UniverseBound where
  nM : ℕ
  pos : 0 < nM
  deriving Repr, DecidableEq

abbrev BoundedFinset (U : UniverseBound) (α : Type*) [DecidableEq α] :=
  { s : Finset α // s.card ≤ U.nM }

namespace BoundedFinset

variable {U : UniverseBound} {α β : Type*} [DecidableEq α] [DecidableEq β]

instance : CoeOut (BoundedFinset U α) (Finset α) := ⟨Subtype.val⟩

omit [DecidableEq α] in
@[simp] theorem val_mk (s : Finset α) (h) :
    ((⟨s, h⟩ : BoundedFinset U α) : Finset α) = s :=
  rfl

@[simp] theorem card_le (s : BoundedFinset U α) : s.1.card ≤ U.nM :=
  s.2

def ofFinset? (U : UniverseBound) (s : Finset α) : Option (BoundedFinset U α) :=
  if h : s.card ≤ U.nM then some ⟨s, h⟩ else none

def empty (U : UniverseBound) : BoundedFinset U α :=
  ⟨∅, by simp⟩

def singleton (U : UniverseBound) (a : α) : BoundedFinset U α :=
  ⟨{a}, by
    have h1 : (1 : ℕ) ≤ U.nM := Nat.succ_le_of_lt U.pos
    simpa using h1⟩

def pair? (U : UniverseBound) (a b : α) : Option (BoundedFinset U α) :=
  ofFinset? U ({a, b} : Finset α)

def sep (s : BoundedFinset U α) (p : α → Prop) [DecidablePred p] : BoundedFinset U α :=
  ⟨s.1.filter p, le_trans (Finset.card_filter_le _ _) s.2⟩

def image (s : BoundedFinset U α) (f : α → β) : BoundedFinset U β :=
  ⟨s.1.image f, le_trans (Finset.card_image_le) s.2⟩

def union? (s t : BoundedFinset U α) : Option (BoundedFinset U α) :=
  ofFinset? U (s.1 ∪ t.1)

def powerset? (s : BoundedFinset U α) : Option (BoundedFinset U (Finset α)) :=
  ofFinset? U s.1.powerset

@[simp] theorem mem_sep {s : BoundedFinset U α} {p : α → Prop} [DecidablePred p] {x : α} :
    x ∈ (sep s p : Finset α) ↔ x ∈ (s : Finset α) ∧ p x := by
  simp [sep]

@[simp] theorem mem_image {s : BoundedFinset U α} {f : α → β} {y : β} :
    y ∈ (image s f : Finset β) ↔ ∃ x ∈ (s : Finset α), f x = y := by
  simp [image]

@[simp] theorem pair?_isSome_singleton_or_pair (a b : α) :
    (pair? U a b).isSome = true ↔ ({a, b} : Finset α).card ≤ U.nM := by
  unfold pair? ofFinset?
  by_cases h : ({a, b} : Finset α).card ≤ U.nM <;> simp [h]

@[simp] theorem union?_isSome (s t : BoundedFinset U α) :
    (union? s t).isSome = true ↔ (s.1 ∪ t.1).card ≤ U.nM := by
  unfold union? ofFinset?
  by_cases h : (s.1 ∪ t.1).card ≤ U.nM <;> simp [h]

@[simp] theorem powerset?_isSome (s : BoundedFinset U α) :
    (powerset? s).isSome = true ↔ s.1.powerset.card ≤ U.nM := by
  unfold powerset? ofFinset?
  by_cases h : s.1.powerset.card ≤ U.nM <;> simp

end BoundedFinset

end HeytingLean.BST
