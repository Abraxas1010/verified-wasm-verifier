import HeytingLean.CategoryTheory.Dialectica.ArchetypeBridge

open _root_.CategoryTheory

example {X Y : HeytingLean.CategoryTheory.Dialectica.Dial (Type)}
    (f : X ⟶ Y) :
    𝟙 X ≫ f = f := by
  exact HeytingLean.CategoryTheory.Dialectica.dial_id_left f
