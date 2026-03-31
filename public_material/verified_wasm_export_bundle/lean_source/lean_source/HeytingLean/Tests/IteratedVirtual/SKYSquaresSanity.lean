import HeytingLean.IteratedVirtual.Examples.SKYSquares

/-!
Compile-only sanity: a `PathHomotopy` yields an arity-1 cell in the SKY-square virtual double category.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open CategoryTheory
open HeytingLean.IteratedVirtual
open HeytingLean.LoF.Combinators.Category

-- Smoke: definition exists.
#check HeytingLean.IteratedVirtual.Examples.skySquares

example (t u : HeytingLean.LoF.Comb) (p q : LSteps t u) (hty : PathHomotopy t u p q) :
    Nonempty
      ((HeytingLean.IteratedVirtual.Examples.skySquares).Cell
        (n := 1)
        (A := HeytingLean.IteratedVirtual.fin2 ⟨t⟩ ⟨u⟩)
        (B := HeytingLean.IteratedVirtual.fin2 ⟨u⟩ ⟨hty.v⟩)
        (v := fun i =>
          match i with
          | ⟨0, _⟩ => q
          | ⟨1, _⟩ => hty.r₁)
        (h := fun i =>
          match i with
          | ⟨0, _⟩ => by
              simpa [HeytingLean.IteratedVirtual.fin2] using p)
        (tgt := hty.r₂)) := by
  refine ⟨?_⟩
  -- The cell type is `PLift (CommSq p q hty.r₁ hty.r₂)`.
  exact PLift.up (HeytingLean.LoF.Combinators.Category.PathHomotopy.toCommSq hty)

end IteratedVirtual
end Tests
end HeytingLean
