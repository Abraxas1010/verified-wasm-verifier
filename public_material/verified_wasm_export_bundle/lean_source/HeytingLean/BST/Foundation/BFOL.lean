import HeytingLean.BST.Foundation.Universe

/-!
# BST.Foundation.BFOL

Bounded first-order quantification over finite carriers.
-/

namespace HeytingLean.BST

def BForall (s : Finset α) (p : α → Prop) : Prop :=
  ∀ x, x ∈ s → p x

def BExists (s : Finset α) (p : α → Prop) : Prop :=
  ∃ x, x ∈ s ∧ p x

instance bforallDecidable (s : Finset α) (p : α → Prop) [DecidablePred p] :
    Decidable (BForall s p) := by
  classical
  unfold BForall
  infer_instance

instance bexistsDecidable (s : Finset α) (p : α → Prop) [DecidablePred p] :
    Decidable (BExists s p) := by
  classical
  unfold BExists
  infer_instance

theorem bforall_excludedMiddle (s : Finset α) (p : α → Prop) [DecidablePred p] :
    BForall s p ∨ ¬ BForall s p := by
  by_cases h : BForall s p <;> simp [h]

theorem bexists_excludedMiddle (s : Finset α) (p : α → Prop) [DecidablePred p] :
    BExists s p ∨ ¬ BExists s p := by
  by_cases h : BExists s p <;> simp [h]

noncomputable def bexistsChoose {s : Finset α} {p : α → Prop} [DecidablePred p]
    (h : BExists s p) : { x // x ∈ s ∧ p x } :=
  ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

theorem bforall_of_subset {s t : Finset α} {p : α → Prop}
    (hst : s ⊆ t) (ht : BForall t p) : BForall s p := by
  intro x hx
  exact ht x (hst hx)

theorem bexists_of_subset {s t : Finset α} {p : α → Prop}
    (hs : BExists s p) (hst : s ⊆ t) : BExists t p := by
  rcases hs with ⟨x, hx, hpx⟩
  exact ⟨x, hst hx, hpx⟩

def BForallOn {U : UniverseBound} [DecidableEq α] (s : BoundedFinset U α) (p : α → Prop) : Prop :=
  BForall (s : Finset α) p

def BExistsOn {U : UniverseBound} [DecidableEq α] (s : BoundedFinset U α) (p : α → Prop) : Prop :=
  BExists (s : Finset α) p

instance bforallOnDecidable {U : UniverseBound} [DecidableEq α]
    (s : BoundedFinset U α) (p : α → Prop) [DecidablePred p] :
    Decidable (BForallOn s p) :=
  bforallDecidable (s := (s : Finset α)) p

instance bexistsOnDecidable {U : UniverseBound} [DecidableEq α]
    (s : BoundedFinset U α) (p : α → Prop) [DecidablePred p] :
    Decidable (BExistsOn s p) :=
  bexistsDecidable (s := (s : Finset α)) p

theorem bforallOn_of_subset {U : UniverseBound} [DecidableEq α]
    {s t : BoundedFinset U α} {p : α → Prop}
    (hst : (s : Finset α) ⊆ (t : Finset α)) (ht : BForallOn t p) : BForallOn s p :=
  bforall_of_subset hst ht

theorem bexistsOn_of_subset {U : UniverseBound} [DecidableEq α]
    {s t : BoundedFinset U α} {p : α → Prop}
    (hs : BExistsOn s p) (hst : (s : Finset α) ⊆ (t : Finset α)) : BExistsOn t p :=
  bexists_of_subset hs hst

noncomputable def bexistsChooseOn {U : UniverseBound} [DecidableEq α]
    {s : BoundedFinset U α} {p : α → Prop}
    [DecidablePred p] (h : BExistsOn s p) : { x // x ∈ (s : Finset α) ∧ p x } :=
  bexistsChoose h

end HeytingLean.BST
