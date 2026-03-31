import HeytingLean.CategoryTheory.Dialectica.ArchetypeBridge
import HeytingLean.CategoryTheory.Polynomial.ArchetypeBridge
import Mathlib.CategoryTheory.Limits.Types.Shapes

namespace HeytingLean
namespace Bridges
namespace Archetype

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Polynomial

/-- Convert a binary product in `Type` from tuple form to categorical product form. -/
noncomputable def toDialProd {A B : Type} : A × B → (A ⨯ B) :=
  (CategoryTheory.Limits.Types.binaryProductIso A B).inv

/-- Convert a Dialectica object over `Type` into a polynomial functor. -/
def dialObjectToPoly (X : CategoryTheory.Dialectica.Dial (Type)) : Poly where
  pos := X.src
  dir := fun _ => X.tgt

/-- Convert a Dialectica morphism over `Type` into a polynomial lens. -/
noncomputable def dialHomToPolymap {X Y : CategoryTheory.Dialectica.Dial (Type)}
    (f : X ⟶ Y) :
    polymap (dialObjectToPoly X) (dialObjectToPoly Y) where
  onPos := f.f
  onDir := fun x y => f.F (toDialProd (A := X.src) (B := Y.tgt) (x, y))

theorem dialHomToPolymap_id (X : CategoryTheory.Dialectica.Dial (Type)) :
    (dialHomToPolymap (𝟙 X)).onPos = id ∧
      (dialHomToPolymap (𝟙 X)).onDir = (fun _ => id) := by
  constructor
  · rfl
  · funext x y
    simp [dialHomToPolymap, toDialProd]

theorem dialHomToPolymap_comp {X Y Z : CategoryTheory.Dialectica.Dial (Type)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (dialHomToPolymap (f ≫ g)).onPos =
      (dialHomToPolymap g).onPos ∘ (dialHomToPolymap f).onPos := by
  rfl

end Archetype
end Bridges
end HeytingLean
