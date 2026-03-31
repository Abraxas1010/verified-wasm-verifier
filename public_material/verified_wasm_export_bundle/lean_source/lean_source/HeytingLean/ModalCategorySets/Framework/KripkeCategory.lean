import HeytingLean.ModalCategorySets.Propositional.Core

namespace HeytingLean.ModalCategorySets.Framework

open HeytingLean.ModalCategorySets.Propositional

universe u v

/-- Minimal category structure needed to induce a Kripke frame from morphism existence. -/
structure KripkeCategory (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id : ∀ X, Hom X X
  comp : ∀ {X Y Z}, Hom X Y → Hom Y Z → Hom X Z

namespace KripkeCategory

variable {Obj : Type u}

/-- Accessibility means existence of a morphism. -/
def toFrame (C : KripkeCategory Obj) : Propositional.Frame Obj where
  rel X Y := Nonempty (C.Hom X Y)

theorem frame_reflexive (C : KripkeCategory Obj) : Propositional.Reflexive C.toFrame := by
  intro X
  exact ⟨C.id X⟩

theorem frame_transitive (C : KripkeCategory Obj) : Propositional.Transitive C.toFrame := by
  intro X Y Z hXY hYZ
  rcases hXY with ⟨f⟩
  rcases hYZ with ⟨g⟩
  exact ⟨C.comp f g⟩

end KripkeCategory

/-- Every successor of `X` in the cone above `X` can access `X` again. -/
def ConeInvertibleAt {Obj : Type u} (C : KripkeCategory Obj) (X : Obj) : Prop :=
  ∀ Y, C.toFrame.rel X Y → C.toFrame.rel Y X

/-- A morphism class on sets. -/
structure MorphismClass where
  admits : {α β : Type u} → (α → β) → Prop
  admits_id : ∀ {α : Type u}, admits (id : α → α)
  admits_comp :
    ∀ {α β γ : Type u} {f : α → β} {g : β → γ},
      admits f → admits g → admits (g ∘ f)

namespace MorphismClass

/-- The induced Kripke category of sets with morphisms restricted by the class. -/
def toKripkeCategory (M : MorphismClass) : KripkeCategory (Type u) where
  Hom α β := Subtype (fun f : α → β => M.admits f)
  id α := by
    exact Subtype.mk (@id α) M.admits_id
  comp := by
    intro X Y Z f g
    exact Subtype.mk (g.1 ∘ f.1) (M.admits_comp f.2 g.2)

end MorphismClass

/-- The thin category whose only morphisms are identities/equalities of objects. -/
def identityCategory : KripkeCategory (Type u) where
  Hom α β := PLift (α = β)
  id α := ⟨rfl⟩
  comp := by
    intro X Y Z f g
    exact ⟨Eq.trans f.down g.down⟩

/-- All functions between sets. -/
def allFunctions : MorphismClass where
  admits := fun _ => True
  admits_id := trivial
  admits_comp := by
    intro α β γ f g hf hg
    trivial

/-- Surjective functions. -/
def surjections : MorphismClass where
  admits := fun f => Function.Surjective f
  admits_id := Function.surjective_id
  admits_comp := by
    intro α β γ f g hf hg
    exact Function.Surjective.comp hg hf

/-- Injective functions. -/
def injections : MorphismClass where
  admits := fun f => Function.Injective f
  admits_id := by
    intro α a₁ a₂ h
    exact h
  admits_comp := by
    intro α β γ f g hf hg
    exact Function.Injective.comp hg hf

/-- Bijections. -/
def bijections : MorphismClass where
  admits := fun f => Function.Bijective f
  admits_id := Function.bijective_id
  admits_comp := by
    intro α β γ f g hf hg
    exact Function.Bijective.comp hg hf

/-- Inclusions are represented by injections in the initial phase. -/
def inclusions : MorphismClass := injections

/-- The pure identity frame on worlds of type `Type u`. -/
def identityFrame : Propositional.Frame (Type u) where
  rel α β := α = β

theorem identityFrame_isIdentityRelation : Propositional.IsIdentityRelation identityFrame := by
  intro α β
  rfl

theorem identityCategory_frame_isIdentityRelation :
    Propositional.IsIdentityRelation identityCategory.toFrame := by
  intro α β
  constructor
  · intro h
    rcases h with ⟨hEq⟩
    exact hEq.down
  · intro hEq
    exact ⟨⟨hEq⟩⟩

end HeytingLean.ModalCategorySets.Framework
