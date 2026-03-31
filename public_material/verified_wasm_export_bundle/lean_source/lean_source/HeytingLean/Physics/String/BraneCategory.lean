import Mathlib.CategoryTheory.Category.Basic
import HeytingLean.Physics.String.DBrane

/-!
# BraneCategory (Track A)

This file provides a *category-shaped* interface for branes/open-string morphisms.

We keep `DBrane.lean` as a tiny demo model, but expose a stable interface layer so later
semantics can replace “counts” with genuine state spaces (chain complexes, modules, etc.).
-/

namespace HeytingLean
namespace Physics
namespace String

universe u v

/-- A brane category: objects are branes; morphisms are open-string state spaces. -/
structure BraneCategory where
  Brane : Type u
  Hom : Brane → Brane → Type v
  id : (A : Brane) → Hom A A
  comp : {A B C : Brane} → Hom A B → Hom B C → Hom A C
  id_comp : ∀ {A B : Brane} (f : Hom A B), comp (id A) f = f
  comp_id : ∀ {A B : Brane} (f : Hom A B), comp f (id B) = f
  assoc : ∀ {A B C D : Brane} (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp (comp f g) h = comp f (comp g h)

namespace BraneCategory

/-- View a `BraneCategory` as a `Category` instance on its object type. -/
def asCategory (B : BraneCategory.{u, v}) : CategoryTheory.Category B.Brane where
  Hom A B' := B.Hom A B'
  id A := B.id A
  comp f g := B.comp f g
  id_comp := by intro A B' f; simpa using B.id_comp f
  comp_id := by intro A B' f; simpa using B.comp_id f
  assoc := by intro A B' C D f g h; simpa using B.assoc f g h

end BraneCategory

/-!
## Toy instance (honest)

We provide a minimal discrete brane category:
- a morphism exists iff the endpoints match.
This keeps the existing `DBrane` story usable without pretending it captures full physics.
-/

namespace Toy

@[simp] def Hom (A B : Brane) : Type :=
  if h : A = B then PUnit else PEmpty

@[simp] def id (A : Brane) : Hom A A := by
  classical
  simp [Hom]

@[simp] def comp {A B C : Brane} : Hom A B → Hom B C → Hom A C := by
  classical
  intro f g
  by_cases hAB : A = B
  · subst hAB
    -- Now `f : Hom B B` is `PUnit`; `g : Hom B C` forces `B = C` if inhabited.
    cases f with
    | unit =>
      exact g
  · -- `Hom A B` is empty
    cases f

theorem id_comp {A B : Brane} (f : Hom A B) : comp (id A) f = f := by
  classical
  by_cases h : A = B
  · subst h
    cases f
    rfl
  · cases f

theorem comp_id {A B : Brane} (f : Hom A B) : comp f (id B) = f := by
  classical
  by_cases h : A = B
  · subst h
    cases f
    rfl
  · cases f

theorem assoc {A B C D : Brane} (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp (comp f g) h = comp f (comp g h) := by
  classical
  -- Everything is subsingleton/empty; brute-force by cases is fine.
  cases f <;> cases g <;> cases h <;> rfl

def discrete : BraneCategory :=
  { Brane := Brane
    Hom := Hom
    id := id
    comp := comp
    id_comp := id_comp
    comp_id := comp_id
    assoc := assoc
  }

end Toy

end String
end Physics
end HeytingLean
