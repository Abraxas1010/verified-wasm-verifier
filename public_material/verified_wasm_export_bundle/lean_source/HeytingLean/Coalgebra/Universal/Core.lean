import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Universal coalgebra (Type) — core

This directory provides a small, executable-first “universal coalgebra” slice for HeytingLean.

We build on Mathlib’s bundled coalgebras of an endofunctor (`CategoryTheory.Endofunctor.Coalgebra`).

Scope:

* Category: `Type u`.
* Endofunctors: `F : Type u ⥤ Type u`.
* Coalgebras: a carrier type `S` with a structure map `S → F S`.

This is deliberately minimal; additional theory (bisimulation, coinduction, quotients) lives in
neighboring files.
-/

namespace HeytingLean
namespace Coalgebra
namespace Universal

open CategoryTheory

universe u

/-- Coalgebras of an endofunctor on `Type`. -/
abbrev Coalg (F : Type u ⥤ Type u) : Type (u + 1) :=
  CategoryTheory.Endofunctor.Coalgebra F

namespace Coalg

variable {F : Type u ⥤ Type u}

/-- Construct a coalgebra from a carrier type and a structure function. -/
def mk (S : Type u) (str : S → F.obj S) : Coalg F :=
  ⟨S, str⟩

@[simp] theorem mk_V (S : Type u) (str : S → F.obj S) : (mk (F := F) S str).V = S :=
  rfl

@[simp] theorem mk_str (S : Type u) (str : S → F.obj S) : (mk (F := F) S str).str = str :=
  rfl

end Coalg

end Universal
end Coalgebra
end HeytingLean

