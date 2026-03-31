import Mathlib.Order.WellFoundedSet

namespace HeytingLean
namespace Hyperseries

/-- Local alias for well-based supports used in hyperseries modules. -/
abbrev WellBased {α : Type*} [Preorder α] (s : Set α) : Prop :=
  s.IsPWO

namespace WellBased

variable {α : Type*} [Preorder α]
variable {s t : Set α}

@[simp] theorem empty : WellBased (∅ : Set α) := by
  simp [WellBased]

@[simp] theorem singleton (a : α) : WellBased ({a} : Set α) := by
  simp [WellBased]

theorem of_subset (ht : WellBased t) (hst : s ⊆ t) : WellBased s :=
  Set.IsPWO.mono ht hst

theorem union (hs : WellBased s) (ht : WellBased t) : WellBased (s ∪ t) := by
  simpa [WellBased] using (Set.IsPWO.union hs ht)

theorem isWF (hs : WellBased s) : s.IsWF := by
  simpa [WellBased] using (Set.IsPWO.isWF hs)

end WellBased
end Hyperseries
end HeytingLean
