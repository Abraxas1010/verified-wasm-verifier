import HeytingLean.CategoryTheory.Dialectica.Basic

namespace HeytingLean
namespace CategoryTheory
namespace Dialectica

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

universe v u

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C]
  [_root_.CategoryTheory.Limits.HasFiniteProducts C]
  [_root_.CategoryTheory.Limits.HasPullbacks C]

theorem dial_id_left {X Y : Dial C} (f : X ⟶ Y) :
    𝟙 X ≫ f = f := by
  simp

theorem dial_id_right {X Y : Dial C} (f : X ⟶ Y) :
    f ≫ 𝟙 Y = f := by
  simp

theorem dial_assoc {W X Y Z : Dial C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  simp

end Dialectica
end CategoryTheory
end HeytingLean
