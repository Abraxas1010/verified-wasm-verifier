import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Types.Basic
import HeytingLean.IteratedVirtual.Examples.FromCategorySquares

/-!
Compile-only sanity checks: `fromCategorySquares` uses `CommSq` as its arity-1 cell type.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open CategoryTheory
open HeytingLean.IteratedVirtual

-- Smoke: the definition exists.
#check HeytingLean.IteratedVirtual.Examples.fromCategorySquares

-- Arity-1 cells are literally `CommSq` (here instantiated at `Type`).
universe u

example {A0 A1 B0 B1 : Type u} (top : A0 ⟶ A1) (left : A0 ⟶ B0) (right : A1 ⟶ B1) (bot : B0 ⟶ B1) :
    Nonempty
        ((HeytingLean.IteratedVirtual.Examples.fromCategorySquares (C := Type u)).Cell
          (n := 1)
          (A := HeytingLean.IteratedVirtual.fin2 A0 A1)
          (B := HeytingLean.IteratedVirtual.fin2 B0 B1)
          (v := fun i =>
            match i with
            | ⟨0, _⟩ => left
            | ⟨1, _⟩ => right)
          (h := fun i =>
            match i with
            | ⟨0, _⟩ => by
                simpa [HeytingLean.IteratedVirtual.fin2] using top)
          (tgt := bot)) ↔ CommSq top left right bot := by
  constructor
  · intro h
    exact h.some.down
  · intro h
    exact ⟨PLift.up h⟩

end IteratedVirtual
end Tests
end HeytingLean
