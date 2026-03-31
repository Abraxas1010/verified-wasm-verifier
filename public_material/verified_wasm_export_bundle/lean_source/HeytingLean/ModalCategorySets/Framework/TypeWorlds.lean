import HeytingLean.ModalCategorySets.Framework.KripkeCategory

namespace HeytingLean.ModalCategorySets.Framework

universe u

/-- A family of set-sized worlds constrained by a predicate on the carrier type. -/
structure ConstrainedType (P : Type u → Prop) where
  carrier : Type u
  property : P carrier

namespace ConstrainedType

variable {P : Type u → Prop}

instance : CoeSort (ConstrainedType P) (Type u) where
  coe X := X.carrier

end ConstrainedType

/-- All functions between the worlds satisfying `P`. -/
def allFunctionsCategory (P : Type u → Prop) :
    KripkeCategory (ConstrainedType P) where
  Hom X Y := X → Y
  id X := id
  comp := by
    intro X Y Z f g
    exact g ∘ f

/-- The category of nonempty sets and arbitrary functions between them. -/
abbrev NonemptyType := ConstrainedType (fun α : Type u => Nonempty α)

def nonemptyFunctionsCategory : KripkeCategory NonemptyType :=
  allFunctionsCategory (P := fun α : Type u => Nonempty α)

theorem nonemptyFunctions_rel (X Y : NonemptyType) :
    nonemptyFunctionsCategory.toFrame.rel X Y := by
  rcases Y.property with ⟨y⟩
  exact ⟨fun _ => y⟩

theorem nonemptyFunctions_coneInvertibleAt (X : NonemptyType) :
    ConeInvertibleAt nonemptyFunctionsCategory X := by
  intro Y hXY
  rcases X.property with ⟨x⟩
  exact ⟨fun _ => x⟩

end HeytingLean.ModalCategorySets.Framework
