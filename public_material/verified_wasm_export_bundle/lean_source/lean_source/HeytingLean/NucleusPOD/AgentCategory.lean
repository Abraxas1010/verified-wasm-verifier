import HeytingLean.NucleusPOD.Foundation
import Mathlib.CategoryTheory.Category.Basic

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 1: The Agent Category and Site
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

open CategoryTheory

instance : SmallCategory Agent where
  Hom A B := Channel A B
  id A := Channel.reflexive A
  comp f g := Channel.compose f g
  id_comp := by
    intro A B f
    exact Channel.compose_reflexive_left f
  comp_id := by
    intro A B f
    exact Channel.compose_reflexive_right f
  assoc := by
    intro A B C D f g h
    exact Channel.compose_assoc f g h

/-- The channel category satisfies left identity. -/
theorem category_id_left {A B : Agent} (f : Channel A B) :
    Channel.compose (Channel.reflexive A) f = f := by
  exact Channel.compose_reflexive_left f

/-- The channel category satisfies right identity. -/
theorem category_id_right {A B : Agent} (f : Channel A B) :
    Channel.compose f (Channel.reflexive B) = f := by
  exact Channel.compose_reflexive_right f

/-- The channel category composition is associative. -/
theorem category_assoc {A B C D : Agent}
    (f : Channel A B) (g : Channel B C) (h : Channel C D) :
    Channel.compose (Channel.compose f g) h = Channel.compose f (Channel.compose g h) := by
  exact Channel.compose_assoc f g h

/-- The same law through Mathlib's `CategoryTheory` interface. -/
theorem categoryTheory_assoc {A B C D : Agent}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  simp

end NucleusPOD
end HeytingLean
