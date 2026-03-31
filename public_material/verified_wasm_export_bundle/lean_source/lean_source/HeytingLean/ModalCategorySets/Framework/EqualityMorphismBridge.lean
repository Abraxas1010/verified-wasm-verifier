import HeytingLean.ModalCategorySets.Framework.EqualityLanguage
import HeytingLean.ModalCategorySets.Framework.KripkeCategory

namespace HeytingLean.ModalCategorySets.Framework

open HeytingLean.ModalCategorySets.Framework.Equality

universe u

/-- Equality-language satisfaction specialized to an actual morphism class. -/
abbrev HoldsIn (M : MorphismClass) {α : Type u} (ρ : Valuation α)
    (φ : EqAssertion) : Prop :=
  Holds M.admits ρ φ

@[simp] theorem MorphismClass.toKripkeCategory_rel_iff (M : MorphismClass) {α β : Type u} :
    M.toKripkeCategory.toFrame.rel α β ↔ Exists (fun f : α → β => M.admits f) := by
  constructor
  · intro h
    rcases h with ⟨f⟩
    exact Exists.intro f.1 f.2
  · intro h
    rcases h with ⟨f, hf⟩
    exact Nonempty.intro (Subtype.mk f hf)

theorem holdsIn_diaQ_of_self_map (M : MorphismClass) {α : Type u} (ρ : Valuation α)
    {φ : EqAssertion} (hφ : HoldsIn M ρ φ) :
    HoldsIn M ρ (.diaQ φ) := by
  refine Exists.intro α ?_
  refine Exists.intro id ?_
  constructor
  · simpa using (M.admits_id : M.admits (id : α → α))
  · simpa using hφ

end HeytingLean.ModalCategorySets.Framework
