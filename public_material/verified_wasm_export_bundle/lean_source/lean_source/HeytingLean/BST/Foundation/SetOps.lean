import HeytingLean.BST.Foundation.BFOL

/-!
# BST.Foundation.SetOps

Lightweight theorems about the initial bounded-set operations.
-/

namespace HeytingLean.BST

namespace BoundedFinset

variable {U : UniverseBound} {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem sep_card_le (s : BoundedFinset U α) (p : α → Prop) [DecidablePred p] :
    (sep s p : Finset α).card ≤ (s : Finset α).card :=
  Finset.card_filter_le _ _

theorem image_card_le (s : BoundedFinset U α) (f : α → β) :
    (image s f : Finset β).card ≤ (s : Finset α).card :=
  Finset.card_image_le

theorem singleton_mem_powerset (s : BoundedFinset U α) {x : α}
    (hx : x ∈ (s : Finset α)) :
    ({x} : Finset α) ∈ s.1.powerset := by
  simpa using Finset.singleton_subset_iff.mpr hx

end BoundedFinset

end HeytingLean.BST
