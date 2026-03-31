import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Universal coalgebra — terminal coalgebras

Mathlib proves a version of Lambek’s lemma for terminal coalgebras:
the structure map of a terminal coalgebra is an isomorphism.

This file re-exports the relevant statement under a stable HeytingLean namespace.
-/

namespace HeytingLean
namespace Coalgebra
namespace Universal

open CategoryTheory

universe u

/-- A coalgebra is final iff it is terminal in the category of `F`-coalgebras. -/
def IsFinal (F : Type u ⥤ Type u) (P : CategoryTheory.Endofunctor.Coalgebra F) : Prop :=
  Nonempty (Limits.IsTerminal P)

/-- Lambek’s lemma (Mathlib): structure map of a terminal coalgebra is an isomorphism. -/
theorem final_str_isIso {F : Type u ⥤ Type u} {P : CategoryTheory.Endofunctor.Coalgebra F}
    (h : IsFinal F P) : IsIso P.str := by
  rcases h with ⟨hT⟩
  exact CategoryTheory.Endofunctor.Coalgebra.Terminal.str_isIso (F := F) hT

end Universal
end Coalgebra
end HeytingLean
