import HeytingLean.IteratedVirtual.Cobordism
import HeytingLean.IteratedVirtual.Examples.FromCategorySquares

/-!
# IteratedVirtual.Examples.CobordismCells

Bridge: a `CobordismOver` witness between parallel iterated cells can be viewed as an
arity-1 cell in the `fromCategorySquares` virtual double category (i.e. a commutative square).
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Examples

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Convert a cobordism witness `A ≫ r₁ = B ≫ r₂` into a commutative-square `Cell` (arity 1). -/
def cobordismAsSquareCell {X Y : C} {n : Nat}
    {A B : IteratedCellOver (C := C) X Y n} (T : CobordismOver (C := C) A B) :
    (fromCategorySquares C).Cell
      (n := 1)
      (A := fin2 X Y)
      (B := fin2 Y T.Z)
      (v := fun i =>
        Fin.cases (motive := fun i => (fin2 X Y i) ⟶ (fin2 Y T.Z i)) B.hom (fun _ => T.r₁) i)
      (h := fun i =>
        Fin.cases
          (motive := fun i : Fin 1 =>
            (fromCategorySquares C).Horiz (fin2 X Y i.castSucc) (fin2 X Y i.succ))
          A.hom
          (fun j => nomatch j) i)
      (tgt := T.r₂) := by
  -- Reduce the `Cell` definition for `n = 1` to `PLift (CommSq ...)`.
  simp [fromCategorySquares, fin2]
  exact ⟨⟨T.comm⟩⟩

end Examples
end IteratedVirtual
end HeytingLean
