import HeytingLean.IteratedVirtual.Examples.FromCategorySquares
import HeytingLean.LoF.Combinators.Category.NFoldCategory

/-!
# IteratedVirtual.Examples.SKYSquares

Instantiates the CommSq-based example on the SKY multiway path category (`MWObj`) and provides
a small helper to build arity-1 cells from existing commuting-square witnesses.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Examples

open CategoryTheory
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

/-- The CommSq-based `VirtualDoubleCategory` instance on the SKY path category. -/
def skySquares : VirtualDoubleCategory :=
  fromCategorySquares (C := MWObj)

/-- Package a `CommSq` witness as an arity-1 cell in `skySquares`. -/
def cellOfCommSq {W X Y Z : MWObj} {top : W ⟶ X} {left : W ⟶ Y} {right : X ⟶ Z} {bot : Y ⟶ Z}
    (sq : CommSq top left right bot) :
    (skySquares).Cell
        (n := 1)
        (A := fin2 W X)
        (B := fin2 Y Z)
        (v := fun i =>
          match i with
          | ⟨0, _⟩ => left
          | ⟨1, _⟩ => right)
        (h := fun i =>
          match i with
          | ⟨0, _⟩ => by
              simpa [fin2] using top)
        (tgt := bot) :=
  PLift.up sq

end Examples
end IteratedVirtual
end HeytingLean

