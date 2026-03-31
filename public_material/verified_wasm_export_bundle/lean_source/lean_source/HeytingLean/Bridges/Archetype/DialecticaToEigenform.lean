import HeytingLean.CategoryTheory.Dialectica.ArchetypeBridge

namespace HeytingLean
namespace Bridges
namespace Archetype

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

universe v u

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C]
  [_root_.CategoryTheory.Limits.HasFiniteProducts C]
  [_root_.CategoryTheory.Limits.HasPullbacks C]

theorem dialectica_assoc_bridge {W X Y Z : CategoryTheory.Dialectica.Dial C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  CategoryTheory.Dialectica.dial_assoc f g h

end Archetype
end Bridges
end HeytingLean
