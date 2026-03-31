import HeytingLean.BST.Foundation.SetOps

/-!
# BST.Foundation.Axioms

The bounded-set-theoretic "axioms" are realized as theorems about the concrete
`BoundedFinset` carrier.
-/

namespace HeytingLean.BST

theorem afb {U : UniverseBound} {α : Type*} [DecidableEq α]
    (s : BoundedFinset U α) : (s : Finset α).card ≤ U.nM :=
  s.2

theorem extensionality {U : UniverseBound} {α : Type*} [DecidableEq α]
    (s t : BoundedFinset U α) :
    s = t ↔ ∀ x, x ∈ (s : Finset α) ↔ x ∈ (t : Finset α) := by
  constructor
  · intro h x
    simp [h]
  · intro h
    apply Subtype.ext
    ext x
    exact h x

theorem bounded_separation {U : UniverseBound} {α : Type*} [DecidableEq α]
    (s : BoundedFinset U α) (p : α → Prop) [DecidablePred p] :
    ∃ t : BoundedFinset U α, ∀ x, x ∈ (t : Finset α) ↔ x ∈ (s : Finset α) ∧ p x := by
  refine ⟨BoundedFinset.sep s p, ?_⟩
  intro x
  simp

theorem bounded_pairing {U : UniverseBound} {α : Type*} [DecidableEq α]
    (a b : α) (h : ({a, b} : Finset α).card ≤ U.nM) :
    ∃ s : BoundedFinset U α, a ∈ (s : Finset α) ∧ b ∈ (s : Finset α) := by
  refine ⟨⟨({a, b} : Finset α), h⟩, ?_⟩
  simp

theorem bounded_union {U : UniverseBound} {α : Type*} [DecidableEq α]
    (s t : BoundedFinset U α) (h : ((s : Finset α) ∪ (t : Finset α)).card ≤ U.nM) :
    ∃ u : BoundedFinset U α, (u : Finset α) = (s : Finset α) ∪ (t : Finset α) := by
  exact ⟨⟨(s : Finset α) ∪ (t : Finset α), h⟩, rfl⟩

theorem bounded_powerset {U : UniverseBound} {α : Type*} [DecidableEq α]
    (s : BoundedFinset U α) (h : (s : Finset α).powerset.card ≤ U.nM) :
    ∃ ps : BoundedFinset U (Finset α), (ps : Finset (Finset α)) = (s : Finset α).powerset := by
  exact ⟨⟨(s : Finset α).powerset, h⟩, rfl⟩

theorem bounded_replacement {U : UniverseBound} {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (s : BoundedFinset U α) (f : α → β) (h : (s.1.image f).card ≤ U.nM) :
    ∃ t : BoundedFinset U β, (t : Finset β) = s.1.image f := by
  exact ⟨⟨s.1.image f, h⟩, rfl⟩

def bstChoose {α : Type*} [DecidableEq α] [LinearOrder α] {U : UniverseBound}
    (s : BoundedFinset U α) (hne : (s : Finset α).Nonempty) : α :=
  (s : Finset α).min' hne

theorem bstChoose_mem {α : Type*} [DecidableEq α] [LinearOrder α] {U : UniverseBound}
    (s : BoundedFinset U α) (hne : (s : Finset α).Nonempty) :
    bstChoose s hne ∈ (s : Finset α) := by
  exact Finset.min'_mem _ _

def bst_choice {α : Type*} [DecidableEq α] [LinearOrder α] {U : UniverseBound}
    (family : Finset (BoundedFinset U α))
    (hne : ∀ s ∈ family, ((s : BoundedFinset U α) : Finset α).Nonempty) :
    ∀ s ∈ family, α :=
  fun s hs => bstChoose s (hne s hs)

theorem bst_choice_mem {α : Type*} [DecidableEq α] [LinearOrder α] {U : UniverseBound}
    (family : Finset (BoundedFinset U α))
    (hne : ∀ s ∈ family, ((s : BoundedFinset U α) : Finset α).Nonempty) :
    ∀ s, ∀ hs : s ∈ family, bst_choice family hne s hs ∈ ((s : BoundedFinset U α) : Finset α) := by
  intro s hs
  exact bstChoose_mem s (hne s hs)

theorem bst_choice_exists {α : Type*} [DecidableEq α] [LinearOrder α]
    (f : α → Finset α) (hne : ∀ a, (f a).Nonempty) :
    ∃ g : α → α, ∀ a, g a ∈ f a := by
  refine ⟨fun a => (f a).min' (hne a), ?_⟩
  intro a
  exact Finset.min'_mem _ _

end HeytingLean.BST
